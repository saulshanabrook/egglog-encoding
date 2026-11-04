#!/usr/bin/env python3
"""Run exact invalid target folds to establish executable negative counterexamples."""
from pathlib import Path
import json
import matrix
BASE=Path(__file__).resolve().parent
ROOT=matrix.ROOT

def main():
    destination=ROOT/'fixtures/invalid-folds';destination.mkdir(parents=True,exist_ok=True)
    results=[]
    for family in ['omitted-tag','omitted-min','omitted-max','reversed-right-tag','changed-right-tag','even-multiplier','wrong-mixed-branch','no-key-context']:
        original=BASE/'fixtures'/f'{family}.bril';source=destination/f'{family}.bril'
        text=original.read_text();assert text.count('br target .unexpected .expected;')==1
        source.write_text(text.replace('br target .unexpected .expected;','jmp .expected;'))
        args=matrix.args_from_source(original)
        results.append(matrix.test('invalid-fold-'+family,'source',source,[{'args':args,'expected_stdout':'7\n'}]))
    (ROOT/'invalid-fold-results.json').write_text(json.dumps(results,indent=2)+'\n')
if __name__=='__main__':main()
