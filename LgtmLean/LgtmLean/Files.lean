module

import all LgtmLean.Basic

def parseFileModificationType : Char → Option ModificationType
| 'M' => some .modified
| 'A' => some .added
| 'D' => some .deleted
| 'T' => some .typechange
| 'R' => some .renamed
| 'C' => some .copied
| _ => none

def formatFileModificationType : ModificationType → String
| .modified => "M"
| .added => "A"
| .deleted => "D"
| .typechange => "T"
| .renamed => "R"
| .copied => "C"
