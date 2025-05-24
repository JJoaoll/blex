

namespace Utils
#eval [ [[2], [3]], [[2, 3]] ].map ([1] :: ·)

def hatter : List (List α) → α → List (List α)
  | [], x => [[x]]
  | xs::xss, x => (x::xs)::xss

#eval [ [[2], [3]], [[2, 3]] ].map (hatter · 1)



instance : Applicative List where
  pure x := [x]
  seq fs u :=
    fs.flatMap (fun f => (u ()).map f)

open List in
def allSingCuts (l : List α) : List (List α × List α) :=
  let r := range l.length
  [(List.splitAt)] <*> r.drop 1 <*> [l  ]

#eval allSingCuts [1, 2, 3, 4]

def allCuts : List α → List (List (List α))
  | [] => []
  | [x] => [[[x]]]
  | x::xs =>
    let xs' := allCuts xs
    xs'.map ([x] :: ·) ++ xs'.map (hatter · x)


end Utils

namespace Regex
inductive Regex where
  | ε
  | char (c : Char)
  | altrn (rx₁ rx₂ : Regex)
  | conct (rx₁ rx₂ : Regex)
  | klosr (rx : Regex)
deriving Repr, Inhabited

open Regex in
def fitsIn (str : String) (rx : Regex) : Bool :=
  match rx with
  | ε => str == ""
  | char c => str == c.toString
  | altrn rx₁ rx₂ => fitsIn str rx₁ || fitsIn str rx₂
  | conct rx₁ rx₂ => (Utils.allSingCuts str.data).any (fun (s₁, s₂) => fitsIn ⟨s₁⟩ rx₁ && fitsIn ⟨s₂⟩ rx₂)
  | klosr rx =>
    let strx := str.data |> Utils.allCuts |> (List.map ∘ List.map) String.mk
    strx.any (·.all (fitsIn · rx))
end Regex

namespace NFA


end NFA


namespace DFA

end DFA

#eval "aaaab"
