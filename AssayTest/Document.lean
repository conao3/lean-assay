import Assay
import Examples.LspTouchstone.Document

/--
info: theorems, run on the original functions:
  T1 replace_keeps_prefix: 573/1000 random inputs satisfy the hypotheses
  T2 replace_keeps_suffix: 573/1000 random inputs satisfy the hypotheses
  T3 replace_inserts: 573/1000 random inputs satisfy the hypotheses
  T4 replace_length: 259/1000 random inputs satisfy the hypotheses
  T5 replace_with_same_is_identity: 558/1000 random inputs satisfy the hypotheses
  T6 replace_whole: 1000/1000 random inputs satisfy the hypotheses

mutant                                      T1  T2  T3  T4  T5  T6   verdict
replaceList := fun _ _ _ _ => default       ✗   ✗   ✗   ✗   ✗   ✗    killed
replaceList := fun _ _ _ _ => nil           ✗   ✗   ✗   ✗   ✗   ✗    killed
replaceList := fun x _ _ _ => x             ·   ✗   ✗   ✗   ·   ✗    killed
replaceList := fun xs _ _ _ => xs.take 1    ✗   ✗   ✗   ✗   ✗   ✗    killed
replaceList := fun xs _ _ _ => xs.reverse   ✗   ✗   ✗   ✗   ✗   ✗    killed
replaceList := fun _ _ _ x => x             ✗   ✗   ✗   ✗   ✗   ·    killed
replaceList := fun _ _ _ xs => xs.take 1    ✗   ✗   ✗   ✗   ✗   ✗    killed
replaceList := fun _ _ _ xs => xs.reverse   ✗   ✗   ✗   ✗   ✗   ✗    killed
replaceList: 4:27: swap the operands of ++  ✗   ✗   ✗   ·   ✗   ·    killed
replaceList: 4:17: swap the operands of ++  ✗   ·   ✗   ·   ✗   ·    killed
replaceList: 4:3: cs.take ↦ cs.drop         ✗   ✗   ✗   ✗   ✗   ✗    killed
replaceList: 4:30: cs.drop ↦ cs.take        ·   ✗   ·   ✗   ✗   ✗    killed

12 mutants: 12 killed, 0 holes, 0 untested, 0 equivalent, 0 stillborn
-/
#guard_msgs in
#assay proved.replaceList
