import Assay
import Examples.Forms.PropDef

set_option assay.timeout 0 in
/--
info: theorems, run on the original functions:
  T1 clampInRange_proven: timed out after 0 inputs, 0 of them satisfying the hypotheses

mutant                                  T1   verdict
clampU8 := fun _ => default             ?    timeout
clampU8 := fun _ => zero                ?    timeout
clampU8: 4:17: swap the branches of if  ?    timeout
clampU8: 4:8: swap the operands of <    ?    timeout
clampU8: 4:8: < ↦ ≤                     ?    timeout
clampU8: 4:8: < ↦ >                     ?    timeout
clampU8: 4:10: 0 ↦ 1                    ?    timeout
clampU8: 4:17: 0 ↦ 1                    ?    timeout
clampU8: 4:40: swap the branches of if  ?    timeout
clampU8: 4:29: > ↦ ≥                    ?    timeout
clampU8: 4:29: > ↦ <                    ?    timeout
clampU8: 4:31: 255 ↦ 256                ?    timeout
clampU8: 4:31: 255 ↦ 254                ?    timeout
clampU8: 4:40: 255 ↦ 256                ?    timeout
clampU8: 4:40: 255 ↦ 254                ?    timeout

15 mutants: 0 killed, 0 holes, 0 untested, 0 equivalent, 15 timed out, 0 stillborn
-/
#guard_msgs in
#assay Forms.clampU8
