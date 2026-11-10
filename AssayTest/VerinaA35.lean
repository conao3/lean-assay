import Assay
import Examples.Verina.A35

/--
info: theorems, run on the original functions:
  T1 majorityElement_spec_satisfied.1: 119/1000 random inputs satisfy the hypotheses
  T2 majorityElement_spec_satisfied.2: 41/30000 random inputs satisfy the hypotheses

mutant                                          T1  T2   verdict
majorityElement := fun _ _ => default           ✗   ✗    killed
majorityElement: 16:34: 0 ↦ 1                   ✗   ✗    killed
majorityElement: 17:40: + ↦ -                   ✗   ✗    killed
majorityElement: 17:42: 1 ↦ 2                   ✗   ✗    killed
majorityElement: 17:42: 1 ↦ 0                   ✗   ✗    killed
majorityElement: 18:48: > ↦ ≥                   ✗   ✗    killed
majorityElement: 18:48: > ↦ <                   ✗   ✗    killed
majorityElement: 18:52: swap the operands of /  ✗   ✗    killed
majorityElement: 18:52: / ↦ *                   ✗   ✗    killed
majorityElement: 18:54: 2 ↦ 1                   ✗   ✗    killed
majorityElement: 19:22: | some (k, _) => k ↦ 0  ✗   ✗    killed

14 mutants: 11 killed, 0 holes, 0 untested, 2 equivalent, 0 timed out, 1 stillborn
-/
#guard_msgs in
#assay Verina.majorityElement
