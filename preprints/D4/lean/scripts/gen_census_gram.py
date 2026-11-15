"""Export exact Gram projection/plane witnesses and degree-six Bernstein checker source.
The generated data are proposals; only kernel-checked Lean identities establish them.
"""
from pathlib import Path
from math import comb
import argparse
ROOT=Path(__file__).resolve().parents[1]
fields=['a','b','c','d','e','f','g']
header='''import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Exact degree-six Bernstein subdivision, with kernel-proved soundness. -/
namespace D4Bound.V7.CensusGram.Bernstein
structure Seven (α : Type) where
'''
s=header+''.join(f'  {x} : α\n' for x in fields)+'  deriving Repr, DecidableEq\n\n'
s+='def Seven.map (f : α → β) (p : Seven α) : Seven β :=\n  ⟨'+', '.join('f p.'+x for x in fields)+'⟩\n\n'
s+='def eval (p : Seven ℝ) (x : ℝ) : ℝ :=\n  '+' + '.join(f'{comb(6,i)}*p.{x}*x^{i}*(1-x)^{6-i}' for i,x in enumerate(fields))+'\n\n'
s+='def good (p : Seven ℤ) : Bool := decide ('+' ∧ '.join('0 ≤ p.'+x for x in fields)+')\n\n'
s+='lemma good_sound (p : Seven ℤ) (h : good p = true) {x : ℝ}\n    (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ eval (p.map Int.cast) x := by\n'
s+='  have hh : '+' ∧ '.join('0 ≤ p.'+x for x in fields)+' := by simpa [good] using h\n'
s+='  rcases hh with ⟨ha,hb,hc,hd,he,hf,hg⟩\n  have hx2 : 0 ≤ 1-x := sub_nonneg.mpr hx1\n  unfold eval Seven.map\n  positivity\n\n'
for name,reverse in [('left',False),('right',True)]:
 vals=[]
 for k in range(7):
  if reverse:terms=[f'{2**k*comb(6-k,j)}*p.{fields[k+j]}' for j in range(7-k)]
  else:terms=[f'{2**(6-k)*comb(k,j)}*p.{fields[j]}' for j in range(k+1)]
  vals.append(' + '.join(terms))
 s+=f'def {name} (p : Seven ℤ) : Seven ℤ :=\n  ⟨'+',\n   '.join(vals)+'⟩\n\n'
 s+=f'lemma eval_{name} (p : Seven ℤ) (x : ℝ) :\n    eval (({name} p).map Int.cast) x = 64*eval (p.map Int.cast) '+('(x/2)' if not reverse else '((x+1)/2)')+' := by\n'
 s+=f'  simp only [eval, Seven.map, {name}]\n  push_cast\n  ring\n\n'
s+='''inductive Tree where
  | leaf
  | split (left right : Tree)
  deriving Repr

def check (p : Seven ℤ) : Tree → Bool
  | .leaf => good p
  | .split l r => check (left p) l && check (right p) r

theorem check_sound (tree : Tree) (p : Seven ℤ) (h : check p tree = true)
    {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ eval (p.map Int.cast) x := by
  induction tree generalizing p x with
  | leaf => exact good_sound p h hx hx1
  | split l r ihl ihr =>
    simp only [check, Bool.and_eq_true] at h
    by_cases hh : x ≤ 1/2
    · have hh := ihl (left p) h.1 (show 0 ≤ 2*x by linarith)
        (show 2*x ≤ 1 by linarith)
      rw [eval_left] at hh
      have he : 2*x/2 = x := by ring
      rw [he] at hh
      linarith
    · have hh := ihr (right p) h.2 (show 0 ≤ 2*x-1 by linarith)
        (show 2*x-1 ≤ 1 by linarith)
      rw [eval_right] at hh
      have he : (2*x-1+1)/2 = x := by ring
      rw [he] at hh
      linarith
end D4Bound.V7.CensusGram.Bernstein
'''
parser=argparse.ArgumentParser()
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
path=ROOT/'D4Bound/V7CensusGramBernstein.lean'
if args.check:
 if path.read_text()!=s:raise SystemExit(f'Generated source mismatch: {path}')
else:path.write_text(s)
print(('PASS: checked' if args.check else 'Generated')+' degree-six Bernstein checker')
