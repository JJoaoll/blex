

namespace Utils
#eval [ [[2], [3]], [[2, 3]] ].map ([1] :: ·)

def hatter : List (List α) → α → List (List α)
  | [], x => [[x]]
  | xs::xss, x => (x::xs)::xss

#eval [ [[2], [3]], [[2, 3]] ].map (hatter · 1)

def Prod.mapSnd (w : α × β) (f : β → γ) : α × γ :=
  ⟨w.1, f w.2⟩

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

open Regex

def r! (str : String) : Regex :=
  match str.data with
  | [] => Regex.ε
  | [c] => Regex.char c
  | c::cs => Regex.ε

end Regex

namespace NFA
-- Gambiarra total!
structure NFA where
  balls : List String              -- representam as calls
  edges : List $ List (Char × Nat)
deriving Repr, Inhabited
-- a lista na porta 0 representa uma seta vinda do nada.
-- a lista na porta 1 representa uma seta saindo de 1.

#eval [1, 2, 3].dropLast ++ [[1, 2, 3].getLast!]
def tst := [[1,2,3], [4,5,6], [7,8,9]]
#eval [[1,2,3], [4,5,6], [7,8,9]].dropLast ++ [0 :: tst.getLast!]

open Regex
open Regex in
def fromRegex : Regex → NFA
  | char c => ⟨[""], [[(c, 0)]]⟩
  | ε => ⟨[""], [[('_', 0)]]⟩
  | altrn rx₁ rx₂ =>
    let M := fromRegex rx₁
    let N := fromRegex rx₂

    let M_ := M.edges.map (·.map (·.map id (· + 1)))
    let N_ := N.edges.map (·.map (·.map id (· + 1 + M.balls.length)))

    let t_len := M.balls.length + N.balls.length + 2 - 1

    NFA.mk
      ("" :: (M.balls ++ N.balls ++ [""]))
      ([('∈', 0)] -- coming from no-where
      :: M_.dropLast ++ [('∈', t_len) :: M_.getLast!]
      ++ N_.dropLast ++ [('∈', t_len) :: N_.getLast!]
      )
  | conct rx₁ rx₂ =>
    let M := fromRegex rx₁
    let N := fromRegex rx₂

    NFA.mk (M.balls ++ N.balls)
           (M.edges ++ N.edges)
  | klosr rx =>
    let M := fromRegex rx
    let new_ending := M.balls.length + 1

    NFA.mk
      (M.balls ++ [""])
      ([('∈', new_ending)] :: M.edges.drop 1 ++ [[('∈', new_ending)]] ++ M.edges.take 1)





-- inductive Regex where
--   | ε
--   | char (c : Char)
--   | altrn (rx₁ rx₂ : Regex)
--   | conct (rx₁ rx₂ : Regex)
--   | klosr (rx : Regex)



end NFA


namespace DFA

end DFA

#eval "aaaab"
