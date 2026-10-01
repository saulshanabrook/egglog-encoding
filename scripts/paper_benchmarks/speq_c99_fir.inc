// Diagnostic-only serialization repair. Never changes the LLVM module.
// The exact fragment is shared by the candidate REV and native analysis harness.
class C99AddressFIR {
  LoopInfo &LI;
  ScalarEvolution &SE;
  DominatorTree &DT;
  Function &F;
  bool Active = false;
  unsigned NextOffset = 0;

  [[noreturn]] void reject(const Twine &Why) const {
    report_fatal_error(Twine("REV C99 address domain: ") + Why);
  }

  bool nonnegative(Value *V, Instruction &At) {
    if (auto *C = dyn_cast<ConstantInt>(V))
      return !C->isNegative();
    return SE.isKnownPredicateAt(ICmpInst::ICMP_SGE, SE.getSCEV(V),
                                SE.getZero(V->getType()), &At);
  }

  // FIR's Int is a mathematical signed integer; its parser erases casts.
  // Establish a conservative range before accepting that erasure or a new sum.
  APInt indexBound(Value *V, Instruction &At) {
    auto *Ty = dyn_cast<IntegerType>(V->getType());
    if (!Ty || (!Ty->isIntegerTy(8) && !Ty->isIntegerTy(32) && !Ty->isIntegerTy(64)))
      reject("FIR supports only scalar i8/i32/i64 integer indices");
    unsigned Width = Ty->getBitWidth();
    APInt Limit = APInt::getSignedMaxValue(Width).zext(128);
    if (auto *C = dyn_cast<ConstantInt>(V)) {
      if (C->isNegative()) reject("negative index");
      return C->getValue().zext(128);
    }
    if (auto *Cast = dyn_cast<CastInst>(V)) {
      if ((!isa<SExtInst>(Cast) && !isa<ZExtInst>(Cast)) ||
          !Cast->getSrcTy()->isIntegerTy() ||
          Cast->getSrcTy()->getIntegerBitWidth() >= Width)
        reject("unsupported index cast");
      // Signed extension preserves the signed value; zero extension does so
      // only under a use-site nonnegativity proof. This domain needs both >=0.
      return indexBound(Cast->getOperand(0), At);
    }
    if (auto *Op = dyn_cast<BinaryOperator>(V)) {
      if (Op->getOpcode() != Instruction::Add &&
          Op->getOpcode() != Instruction::Mul)
        reject("unsupported index arithmetic");
      APInt A = indexBound(Op->getOperand(0), At);
      APInt B = indexBound(Op->getOperand(1), At);
      APInt Bound = Op->getOpcode() == Instruction::Add ? A + B : A * B;
      if (Bound.ugt(Limit)) reject("index arithmetic may wrap");
      return Bound;
    }
    if (!isa<Argument>(V) && !isa<PHINode>(V))
      reject("index depends on memory or an unsupported instruction");
    if (!nonnegative(V, At))
      reject("missing use-site signed nonnegativity proof");
    return Limit;
  }

  void checkCast(CastInst &Cast, Instruction &At) {
    if (!Cast.getSrcTy()->isIntegerTy() || !Cast.getDestTy()->isIntegerTy() ||
        (!isa<SExtInst>(Cast) && !isa<ZExtInst>(Cast)) ||
        (!Cast.getSrcTy()->isIntegerTy(8) && !Cast.getSrcTy()->isIntegerTy(32)) ||
        (!Cast.getDestTy()->isIntegerTy(32) && !Cast.getDestTy()->isIntegerTy(64)) ||
        Cast.getSrcTy()->getIntegerBitWidth() >=
            Cast.getDestTy()->getIntegerBitWidth())
      reject("FIR cannot preserve this cast");
    if (isa<ZExtInst>(Cast) && !nonnegative(Cast.getOperand(0), At))
      reject("zero extension lacks a use-site nonnegativity proof");
  }

  void closeOperand(Value *V, Instruction &Use, raw_ostream &OS,
                    SmallPtrSetImpl<Instruction *> &Emitted) {
    auto *I = dyn_cast<Instruction>(V);
    if (!I || LI.getLoopFor(I->getParent())) return;
    if (!DT.dominates(I, &Use)) reject("external definition does not dominate use");
    // Validate at each use, even if the same definition was already emitted.
    if (auto *Cast = dyn_cast<CastInst>(I)) {
      checkCast(*Cast, Use);
    } else if (auto *Op = dyn_cast<BinaryOperator>(I)) {
      if (!Op->getType()->isIntegerTy() ||
          (Op->getOpcode() != Instruction::Add &&
           Op->getOpcode() != Instruction::Mul))
        reject("external definition is not supported pure integer arithmetic");
      (void)indexBound(Op, Use);
    } else {
      reject("external definition is not a supported pure cast/add/mul");
    }
    for (Value *Operand : I->operands()) closeOperand(Operand, Use, OS, Emitted);
    if (Emitted.insert(I).second) OS << *I << "\n";
  }

public:
  C99AddressFIR(LoopInfo &LI, ScalarEvolution &SE, DominatorTree &DT,
                Function &F, bool Selected) : LI(LI), SE(SE), DT(DT), F(F) {
    if (!Selected) return;
    for (Argument &A : F.args())
      if (A.getName().starts_with("reproduction.c99."))
        reject("reserved diagnostic temporary name already exists");
    for (BasicBlock &BB : F)
      for (Instruction &I : BB) {
        if (I.getName().starts_with("reproduction.c99."))
          reject("reserved diagnostic temporary name already exists");
        if (auto *G = dyn_cast<GetElementPtrInst>(&I))
          Active |= isa<GetElementPtrInst>(G->getPointerOperand());
      }
    if (!Active) reject("selected function has no chained GEP");
  }

  // Only fallback typing for a function needing this repair. Existing tensor
  // metadata remains the first choice in REV; unchanged flat references bypass it.
  std::string memoryType(Value *Root) {
    if (!Active) return "";
    if (!Root || !isa<Argument>(Root) ||
        !Root->getType()->isPointerTy() || Root->getType()->getPointerAddressSpace())
      reject("memory root is not an address-space-zero argument");
    SmallVector<Value *> Work{Root};
    SmallPtrSet<Value *, 16> Seen;
    bool Accessed = false;
    while (!Work.empty()) {
      Value *P = Work.pop_back_val();
      if (!Seen.insert(P).second) continue;
      for (User *U : P->users()) {
        if (auto *G = dyn_cast<GetElementPtrInst>(U)) {
          if (G->getPointerOperand() != P || G->getNumIndices() != 1 ||
              !G->getSourceElementType()->isDoubleTy() || !G->isInBounds())
            reject("memory root has an incompatible GEP");
          Work.push_back(G);
        } else if (auto *L = dyn_cast<LoadInst>(U)) {
          if (L->getPointerOperand() != P || !L->getType()->isDoubleTy() ||
              L->isVolatile() || L->isAtomic())
            reject("memory root has an incompatible load");
          Accessed = true;
        } else if (auto *S = dyn_cast<StoreInst>(U)) {
          if (S->getPointerOperand() != P ||
              !S->getValueOperand()->getType()->isDoubleTy() ||
              S->isVolatile() || S->isAtomic())
            reject("memory root has an incompatible store");
          Accessed = true;
        } else {
          reject("memory root escapes or has an unsupported use");
        }
      }
    }
    if (!Accessed) reject("memory root has no typed access");
    return "ptr 1 double";
  }

  void prelude(Loop &L, raw_ostream &OS) {
    if (!Active) return;
    SmallPtrSet<Instruction *, 16> Emitted;
    for (BasicBlock *BB : L.blocks()) {
      if (LI.getLoopFor(BB) != &L) continue;
      for (Instruction &I : *BB) {
        if (isa<PHINode>(&I) || I.isTerminator()) continue;
        for (Value *Operand : I.operands()) closeOperand(Operand, I, OS, Emitted);
      }
    }
  }

  // Return true only when the original serializer should skip this instruction.
  bool emit(Instruction &I, raw_ostream &OS) {
    if (!Active) return false;
    if (auto *Cast = dyn_cast<CastInst>(&I)) {
      checkCast(*Cast, I);
      return false; // Preserve the actual cast in FIR/evidence.
    }
    auto *G = dyn_cast<GetElementPtrInst>(&I);
    if (!G) return false;
    if (F.getParent()->getDataLayout().getIndexSizeInBits(0) != 64)
      reject("requires a 64-bit pointer index layout");
    SmallVector<Value *> Indices;
    Value *Base = G;
    APInt Bound(128, 0);
    while (auto *Part = dyn_cast<GetElementPtrInst>(Base)) {
      if (!Part->isInBounds() || Part->getNumIndices() != 1 ||
          !Part->getSourceElementType()->isDoubleTy() ||
          Part->getPointerAddressSpace() != 0)
        reject("only inbounds same-double scalar GEP chains are supported");
      Value *Index = Part->getOperand(1);
      if (!Index->getType()->isIntegerTy(64)) reject("GEP index is not i64");
      Bound += indexBound(Index, I);
      if (Bound.ugt(APInt::getSignedMaxValue(64).zext(128)))
        reject("combined GEP offset may wrap");
      Indices.push_back(Index);
      Base = Part->getPointerOperand();
    }
    if (!isa<Argument>(Base) || Base->getType()->getPointerAddressSpace())
      reject("GEP chain has no supported argument root");
    // Read-only roots matter too: typing only the mutable root could miss an
    // incompatible load through A/B while flattening its address.
    (void)memoryType(Base);
    if (Indices.size() == 1) return false;
    // No LLVM instruction is inserted. New FIR sums are representable integers,
    // justified above independently of the original nsw/nuw flags.
    std::string Offset;
    raw_string_ostream First(Offset);
    Indices.back()->printAsOperand(First, false);
    for (auto It = Indices.rbegin() + 1; It != Indices.rend(); ++It) {
      std::string Name = "%reproduction.c99.offset." + std::to_string(NextOffset++);
      OS << "  " << Name << " = add nsw i64 " << Offset << ", ";
      (*It)->printAsOperand(OS, false);
      OS << "\n";
      Offset = Name;
    }
    OS << "  "; I.printAsOperand(OS, false);
    OS << " = getelementptr inbounds double, ptr ";
    Base->printAsOperand(OS, false);
    OS << ", i64 " << Offset << "\n";
    return true;
  }
};
