import Assay
import Examples.Forms.Precond

/--
info: theorems, run on the original functions:
  T1 headOr_spec_satisfied: 876/1000 random inputs satisfy the hypotheses
  T2 maxOf_spec_satisfied: 335/1000 random inputs satisfy the hypotheses
  T3 lastOf_spec_satisfied: 876/1000 random inputs satisfy the hypotheses

mutant                              T1  T2  T3   verdict
headOr := fun _ _ => default        ✗   -   -    killed
headOr := fun _ _ => zero           ✗   -   -    killed
headOr: 8:15: | x :: _ => x ↦ 0     ✗   -   -    killed
maxOf := fun _ _ => default         -   ✗   -    killed
maxOf := fun _ _ => zero            -   ✗   -    killed
maxOf: 22:12: max ↦ min             -   ✗   -    killed
lastOf := fun _ _ => default        -   -   ✗    killed
lastOf := fun _ _ => zero           -   -   ✗    killed
lastOf: 34:3: xs.getLast ↦ xs.head  -   -   ·    HOLE

12 mutants: 8 killed, 1 holes, 0 untested, 2 equivalent, 0 timed out, 1 stillborn
---
warning: hole: `lastOf: 34:3: xs.getLast ↦ xs.head` satisfies every theorem but changes the output on an input that satisfies the hypotheses of lastOf_spec_satisfied: xs := [0, 2]
-/
#guard_msgs in
#assay Forms.headOr Forms.maxOf Forms.lastOf
