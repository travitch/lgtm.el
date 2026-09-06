module

import all LgtmLean.Basic

def parseFileModificationType (c : Char) : Option ModificationType :=
match c with
| 'M' => some .modified
| 'A' => some .added
| 'D' => some .deleted
| 'T' => some .typechange
| 'R' => some .renamed
| 'C' => some .copied
| _ => none

def formatFileModificationType (t : ModificationType) : String :=
match t with
| .modified => "M"
| .added => "A"
| .deleted => "D"
| .typechange => "T"
| .renamed => "R"
| .copied => "C"
