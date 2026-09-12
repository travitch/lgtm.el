module

public import LgtmLean.Basic

/-- Attempt to parse C as a git file modification type. -/
public def parseFileModificationType (c : Char) : Option ModificationType :=
match c with
| 'M' => some .modified
| 'A' => some .added
| 'D' => some .deleted
| 'T' => some .typechange
| 'R' => some .renamed
| 'C' => some .copied
| _ => none

public def formatFileModificationType (m : ModificationType) : String :=
match m with
| .modified => "M"
| .added => "A"
| .deleted => "D"
| .typechange => "T"
| .renamed => "R"
| .copied => "C"
