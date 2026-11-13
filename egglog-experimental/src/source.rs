//! Composition of source passes; neither pass depends on the other's internals.
use crate::{
    DisequalityCompiler,
    slotted::{self, CompileError, CompiledProgram, Options},
};

/// Compile the extended source language by lowering injectivity/disequality first,
/// then passing the resulting ordinary rewrites and schedules to slotted.
#[derive(Clone, Default)]
pub struct SlottedCompiler {
    disequality: DisequalityCompiler,
    slotted: slotted::Compiler,
}

impl SlottedCompiler {
    /// Start with an empty source environment.
    pub fn new(options: Options) -> Self {
        Self {
            slotted: slotted::Compiler::new(options),
            ..Default::default()
        }
    }

    /// Reuse an existing slotted graph's parsing vocabulary.
    pub fn for_egraph(options: Options, graph: &egglog::EGraph) -> Self {
        Self {
            slotted: slotted::Compiler::for_egraph(options, graph),
            ..Default::default()
        }
    }

    /// Compile both passes transactionally to ordinary egglog text.
    pub fn compile(
        &mut self,
        filename: Option<String>,
        source: &str,
    ) -> Result<String, CompileError> {
        let mut next = self.clone();
        let source = next.disequality.compile(filename.clone(), source)?;
        let result = next.slotted.compile(filename, &source)?;
        *self = next;
        Ok(result)
    }

    /// Compile both passes transactionally, retaining the lowered source proof theory.
    pub fn compile_program(
        &mut self,
        filename: Option<String>,
        source: &str,
    ) -> Result<CompiledProgram, CompileError> {
        let mut next = self.clone();
        let source = next.disequality.compile(filename.clone(), source)?;
        let result = next.slotted.compile_program(filename, &source)?;
        *self = next;
        Ok(result)
    }
}
