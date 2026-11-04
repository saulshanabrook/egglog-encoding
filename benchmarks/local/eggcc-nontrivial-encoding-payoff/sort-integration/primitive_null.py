#!/usr/bin/env python3
"""Execute the primitive-column null over the exact compiler seed-graph receipt."""
from pathlib import Path
import hashlib,itertools,json,re
BASE=Path(__file__).resolve().parent

def parse(text):
    tokens=iter(re.findall(r'\(|\)|[^\s()]+',text))
    def expression(token):
        if token!='(': return token
        items=[]
        for following in tokens:
            if following==')': return items
            items.append(expression(following))
        raise AssertionError('unclosed expression')
    return [expression(token) for token in tokens]

def main():
    rows=json.loads((BASE/'positive-results.json').read_text())
    modes={row['mode']:row for row in rows}
    def accepted(mode):
        selected=[q for q in modes[mode]['queries'] if q.get('accepted')]
        assert selected
        assert len({q['program'] for q in selected})==1
        return selected[0]
    primitive=accepted('primitive-only');encoding=accepted('encoding');seed=accepted('seed-only')
    program=primitive['program'];forms=parse(program)
    encoded_forms=parse(encoding['program'])
    assert forms==[form for form in encoded_forms if form[0]!='run-schedule']
    assert forms==parse(seed['program'])
    assert all(form[0]!='run-schedule' for form in forms)
    assert primitive['injectivity_saturated']==False and primitive['engine_witness_queries_run']==False
    assert primitive['manual_closure_run']==False and primitive['export']==False
    sorts={form[1] for form in forms if form[0]=='datatype'}
    declarations={}
    for form in forms:
        if form[0]=='constructor': declarations[form[1]]={'fields':form[2],'output_sort':form[3]}
        if form[0]=='datatype':
            for variant in form[2:]:declarations[variant[0]]={'fields':variant[1:],'output_sort':form[1]}
    applications=[]
    def visit(term,identity):
        if not isinstance(term,list):return
        name=term[0];fields=declarations[name]['fields'];assert len(term)-1==len(fields)
        primitive_fields={}
        for index,(sort,value) in enumerate(zip(fields,term[1:])):
            if sort not in sorts:
                assert sort=='i64' and isinstance(value,str) and re.fullmatch(r'-?\d+',value)
                primitive_fields[index]=int(value)
            elif isinstance(value,list):visit(value,identity+f'.{index}')
        applications.append({'identity':identity,'constructor':name,'primitive_fields':primitive_fields})
    for form in forms:
        if form[0]=='let':visit(form[2],form[1])
    comparisons=[]
    for left,right in itertools.product(applications,repeat=2):
        if left['constructor']!=right['constructor']:continue
        for index,lvalue in left['primitive_fields'].items():
            rvalue=right['primitive_fields'][index]
            comparisons.append({'constructor':left['constructor'],'left':left['identity'],'right':right['identity'],'column':index,'left_primitive':lvalue,'right_primitive':rvalue,'equal':lvalue==rvalue})
    mismatches=[row for row in comparisons if not row['equal']]
    assert comparisons and not mismatches
    target_primitive_mismatch=any(row['constructor']=='OddMul' and not row['equal'] for row in comparisons)
    assert target_primitive_mismatch==False
    result={'status':'passed','implementation':'external primitive-column comparison pass; Rust PrimitiveOnly retains and emits the unchanged seed graph','program_sha256':hashlib.sha256(program.encode()).hexdigest(),'encoding_program_sha256':hashlib.sha256(encoding['program'].encode()).hexdigest(),'positive_results_sha256':hashlib.sha256((BASE/'positive-results.json').read_bytes()).hexdigest(),'binary_sha256':hashlib.sha256((BASE/'bin/eggcc').read_bytes()).hexdigest(),'graph_equal_after_removing_only_encoding_run_schedule':True,'seed_only_graph_identical':True,'schemas':declarations,'applications':applications,'primitive_comparisons':comparisons,'primitive_mismatches':mismatches,'equality_sort_comparison_or_propagation':False,'final_primitive_target_witness':target_primitive_mismatch,'export':False}
    (BASE/'primitive-null.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'passed','application_rows':len(applications),'primitive_comparisons':len(comparisons),'primitive_mismatches':len(mismatches),'final_primitive_target_witness':False}))
if __name__=='__main__':main()
