-- @[default_instance]
-- instance : Coe (Id α) α where
--   coe x := x
-- def fromId (x : Id α) : α := x

-- @[default_instance]
-- instance [Add α] : HAdd (Id α) α α where
--   hAdd x y := fromId x + y

-- def test : Id Int := do {
--   let x ← 3
--   let y ← 4

--   return x + y
-- }


namespace Utils
-- [ [[2], [3]], [[2, 3]] ]
-- [ [[1], [2], [3]], [[1], [2, 3]] ]
#eval [ [[2], [3]], [[2, 3]] ].map ([1] :: ·)
-- [ [[1, 2], [3]], [[1, 2, 3]] ]

def hatter : List (List α) → α → List (List α)
  | [], x => [[x]]
  | xs::xss, x => (x::xs)::xss

#eval [ [[2], [3]], [[2, 3]] ].map (hatter · 1)

-- [[2,3,4]], [[2], [3, 4]], [[2, 3], [4]]
-- maldita lean, n tinha splat da list (fiz errado, mas fiz :PPP)


instance : Applicative List where
  pure x := [x]
  seq fs u :=
    fs.flatMap (fun f => (u ()).map f)
-- seq : {α β : Type u} → f (α → β) → (f α → f β)
-- seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
-- fs.bind (fun f => xs.map f)

#check List.flatMap
#eval [(· + 2), (· + 1)].flatMap (fun f => [1, 2, 3].map f)
#eval (· + 5) <$> List.range 5
#eval [(· + 2)] <*> List.range 5
#check @List.splitAt
#check @List.zipWith Nat Char (List Char × List Char)
#check @List.zipWith Nat (List Char) (List Char × List Char) (List.splitAt) [1, 2, 3] ["oi, tudo".data, "tchau".data]
#eval @List.zipWith Nat (List Char) (List Char × List Char) (List.splitAt) [1, 2, 3] ["oi, tudo".data, "tchau".data, "blah".data]
#eval [1, 2, 3, 4].splitAt 3
#check @List.zipWith Nat Nat Nat (· + ·) [1, 2] [1, 2, 3]
#check "oi".data
#check List.splitAt
#check ([fun n => List.splitAt n] <*> (List.range 5)) <*> ["oi, tudo bom".data]
#eval ([fun n => List.splitAt n] <*> (List.range 2)) <*> ["oi, tudo bom".data]
#check ([fun n => List.splitAt n] <*> (List.range 2)) <*> ["oi, tudo bom".data] |> (·.map (·.map String.mk String.mk))
#eval ([fun n => List.splitAt n] <*> (List.range 2)) <*> ["oi, tudo bom".data] |> (·.map (·.map String.mk String.mk))
#check [(· + ·)] <*> [3, 4, 5]
#eval [(· + ·)] <*> [3, 4, 5] <*> [1]
#eval [(· + 2), (· * 3)] <*> [1]

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


#eval allCuts [1, 2, 3]
#eval allCuts [1, 2, 3, 4]
#eval "oi, mundo".data |> allCuts |> (List.map ∘ List.map) String.mk
#check "oi, mundo".data |> allCuts |> (List.map ∘ List.map) String.mk |> (·.all (fun ss => ss.all (fun _ => true)))
#check List.all


end Utils

-- #check Id.map_eq test (· + 2)
-- #check Id.eq_1
-- #check (test : Int)
-- #eval (test : Int) + 4
-- #eval (3 : Int) + 4
-- #check test

-- simpler impossible
namespace Regex
inductive Regex where
  | ε
  | char (c : Char)
  | altrn (rx₁ rx₂ : Regex)
  | conct (rx₁ rx₂ : Regex)
  | klosr (rx : Regex)
deriving Repr, Inhabited

#eval [1:3]


-- (Inicially) i'll treat regex as booleans
-- preds.
open Regex in
def fitsIn (str : String) (rx : Regex) : Bool :=
  match rx with
  | ε => str == ""
  | char c => str == c.toString
  | altrn rx₁ rx₂ => fitsIn str rx₁ || fitsIn str rx₂
  | conct rx₁ rx₂ => (Utils.allSingCuts str.data).any (fun (s₁, s₂) => fitsIn ⟨s₁⟩ rx₁ && fitsIn ⟨s₂⟩ rx₂)

    -- let isConctOf : Id Bool := do {
    --   let xs  ← str.data
    --   let len ← xs.length

    --   for i in [len] do {
    --     if fitsIn ⟨xs.take i⟩ rx₁ && fitsIn ⟨xs.drop i⟩ rx₂ then
    --       return true
    --     -- ['a', 'b']
    --     -- "a" "b"
    --   }

    --   return false
    -- }


  | klosr rx =>
    let strx := str.data |> Utils.allCuts |> (List.map ∘ List.map) String.mk
    strx.any (·.all (fitsIn · rx))


open Regex
def r₁ := char 'a'
def r₂ := char 'b'
def r₃ := altrn r₁ r₂
def r₄ := conct r₃ r₂
def r₅ := klosr r₄

-- notation part
#eval fitsIn "a" r₁
#eval fitsIn "b" r₁
#eval fitsIn "b" r₁
#eval fitsIn "b" r₂
#eval fitsIn "a" r₃
#eval fitsIn "b" r₃
#eval fitsIn "c" r₃
#eval fitsIn "a" r₄
#eval fitsIn "b" r₄
#eval fitsIn "ab" r₄
#eval fitsIn "ab" (conct r₁ r₂)
#eval fitsIn "aaaaaaa" (klosr $ char 'a')
#eval fitsIn "aaaaaaa" (klosr (altrn r₁ r₂))
#eval fitsIn "aabbaba" (klosr (altrn r₁ r₂))
#eval fitsIn "cabbaba" (klosr (altrn r₁ r₂))
#eval fitsIn "cabbaba" (klosr (conct r₁ r₂))
#eval fitsIn "abababababab" (klosr (conct r₁ r₂))
#eval fitsIn "ababababababa" (klosr (conct r₁ r₂))
#eval fitsIn "abbbabbb" (klosr (conct r₃ r₂))

-- -- p/ ñ abusar das Strings vazias, serão Option's!
-- inductive Ball
--   | ball (call : Option String)
-- deriving Repr, Inhabited

-- inductive MultiArr
--   | arrs (p : Char → Bool)
-- -- | arrs (as : List Char) -- another option
-- deriving Inhabited

-- structure NFA where
--   circ : Ball
--   eggs : List (MultiArr × NFA)
-- deriving Inhabited

-- -- ex. pag 24
-- open NFA MultiArr in
-- def tL :=
--   NFA.mk (Ball.ball none) [(arrs (· == 'a'),
--     NFA.mk (Ball.ball none) [(arrs (· == 'a'),
--       )]) ]
-- #check NFA.mk (Ball.ball $ some "1") []


-- -- TIREI UNIVERSOS PQ DAVA ERRO NA HORA DE EXIBIR!
-- structure Ball where
--   call? : Option String
-- deriving Repr, Inhabited

-- #check 'ε'
-- -- TODO: PROJECTIONS
-- inductive Arr : Nat → Type u where
--   | mk (c : Char) (head : Fin (n + 1)) : Arr n -- head: ending state.
--   -- this n + 1 is explained above.
-- deriving Repr, Inhabited

-- #eval (⟨0, by decide⟩ : Fin 1)
-- -- #eval (⟨1, by decide⟩ : Fin 1) --> doesnt work

--  -- TODO: Talvez tenha problemas por off_by_one :P
-- inductive NFA : Nat → Type where
--   | mk (circs : Vector Ball n) (edges : Vector (List $ Arr $ n) (n+1)) : NFA n
--   -- circs : List Ball       -- A pos na Lista vira id
--   -- edges : List (List Arr) -- A pos diz de onde vem as setas
-- deriving Repr, Inhabited

-- #check (Vector.mk #[] (by decide) : Vector Nat 0)
-- -- #eval (NFA.mk (Vector.mk #[] (by decide)) (Vector.mk #[] (by decide)) : NFA 0)
-- def tst1 : Vector (List $ Arr 0) 0 := Vector.mk #[] (by simp)

-- #check (NFA.mk (Vector.mk #[Ball.mk none] (by decide)) (Vector.mk #[[], []] (by decide)) : NFA 1)
-- #eval (NFA.mk (Vector.mk #[Ball.mk none] (by decide))
--   (Vector.mk #[[Arr.mk '∈' 0, Arr.mk '∈' 0], []] (by decide)) : NFA 1)

-- #eval (NFA.mk (Vector.mk #[Ball.mk none, Ball.mk $ some "", Ball.mk $ some ""] (by decide))
--   (Vector.mk #[[Arr.mk '∈' ⟨1, by decide⟩, Arr.mk '∈' ⟨2, by decide⟩], [], [], []] (by decide)) : NFA 3)

-- --                           1      2       3        4       5        6
-- #eval (NFA.mk (Vector.mk #[⟨none⟩, ⟨none⟩, ⟨some ""⟩, ⟨none⟩, ⟨some ""⟩, ⟨none⟩] (by decide))
--   (Vector.mk #[
-- /- 0 -/ [⟨'_', 4⟩],
-- /- 1 -/ [⟨'a', 3⟩],
-- /- 2 -/ [⟨'a', 1⟩],
-- /- 3 -/ [⟨'a', 2⟩],
-- /- 4 -/ [⟨'∈', 3⟩, ⟨'∈', 5⟩]
-- /- 5 -/ [⟨'a', ⟨6, by decide⟩⟩],
-- /- 6 -/ [⟨'a', 5⟩]
--   ] (by decide)) : NFA 6)


-- -- inductive NFA : Nat → Type where
-- --   | mk (circs : Vector Ball n) (edges : Vector (List $ Arr $ n-1) n) : NFA n


-- -- i'll abuse the 0 to represent a
-- -- edge coming from no-where, because im
-- -- lazy
-- -- TODO: learn how to deal with final states
-- def Regex.toNFA (rx : Regex) : (n : Nat) × NFA n :=
--   match rx with                                                                  -- decide just failed
--   | char c => ⟨1, NFA.mk (Vector.mk #[⟨none⟩] (by decide)) (Vector.mk #[[⟨c, 1⟩], []] (by simp))⟩
--   | ε => ⟨1, NFA.mk (Vector.mk #[⟨none⟩] (by decide)) (Vector.mk #[[⟨'∈', 1⟩], []] (by decide))⟩
--   | altrn rx₁ rx₂ =>
--     let nf₁ := rx₁.toNFA
--     let nf₂ := rx₂.toNFA
--     sorry

--   | conct Mx Nx =>
--     let M := rx₁.toNFA
--     let N := rx₂.toNFA
--     match M, N with
--     | ⟨⟨xs, _xs⟩, ⟨ys, _ys⟩ =>



--   | klosr rx => sorry

-- -- inductive MultiArr
-- -- -- | arrs (p : Char → Bool)
-- --   | arrs (as : List Char) -- another option
-- -- deriving Repr, Inhabited
 -- isso so vai ficar temporariamente salvo no gh






-- inductive NFA where
--   | L (l : NFA)
--   | R (r : NFA)
--   | LR (l r : NFA)
--   | _





end Regex

#eval "aaaab"
