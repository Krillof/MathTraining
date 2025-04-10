import Mathlib.Tactic -- Use always
import Mathlib.Util.Delaborators -- Use always

import Mathlib.Topology.Basic

open Topology

set_option warningAsError false -- Use always
set_option diagnostics true

#check IsOpen.inter -- First axiom
#check isOpen_univ -- Second axiom
#check isOpen_sUnion -- Third axiom
