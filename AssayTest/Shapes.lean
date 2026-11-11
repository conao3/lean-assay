import Assay
import Examples.Forms.Shapes

/--
info: theorems, run on the original functions:
  T1 indexFound_proven: 1000/1000 random inputs satisfy the hypotheses
  T2 toNatOk_ok: 526/1000 random inputs satisfy the hypotheses
  T3 toNatOk_cases: 1000/1000 random inputs satisfy the hypotheses

mutant                                   T1  T2  T3   verdict
indexOf := fun _ _ _ _ => default        ✗   -   -    killed
indexOf := fun _ _ _ _ => none           ✗   -   -    killed
indexOf: 7:31: swap the branches of if   ✗   -   -    killed
indexOf: 7:21: == ↦ !=                   ✗   -   -    killed
indexOf: 7:36: 0 ↦ 1                     ·   -   -    HOLE
indexOf: 7:65: + ↦ -                     ·   -   -    HOLE
indexOf: 7:67: 1 ↦ 2                     ·   -   -    HOLE
indexOf: 7:67: 1 ↦ 0                     ·   -   -    HOLE
toNatOk := fun _ => default              -   ✗   ✗    killed
toNatOk: 16:17: swap the branches of if  -   ✗   ✗    killed
toNatOk: 16:8: swap the operands of <    -   ✗   ✗    killed
toNatOk: 16:8: < ↦ ≤                     -   ✗   ✗    killed
toNatOk: 16:8: < ↦ >                     -   ✗   ✗    killed
toNatOk: 16:10: 0 ↦ 1                    -   ✗   ✗    killed

16 mutants: 10 killed, 4 holes, 0 untested, 0 equivalent, 0 timed out, 2 stillborn
---
warning: hole: `indexOf: 7:36: 0 ↦ 1` satisfies every theorem but changes the output on an input that satisfies the hypotheses of indexFound_proven: x := -1, xs := [-1]
---
warning: hole: `indexOf: 7:65: + ↦ -` satisfies every theorem but changes the output on an input that satisfies the hypotheses of indexFound_proven: x := -1, xs := [-2, -1]
---
warning: hole: `indexOf: 7:67: 1 ↦ 2` satisfies every theorem but changes the output on an input that satisfies the hypotheses of indexFound_proven: x := -1, xs := [-2, -1]
---
warning: hole: `indexOf: 7:67: 1 ↦ 0` satisfies every theorem but changes the output on an input that satisfies the hypotheses of indexFound_proven: x := -1, xs := [-2, -1]
-/
#guard_msgs in
#assay Forms.Shapes.indexOf Forms.Shapes.toNatOk
