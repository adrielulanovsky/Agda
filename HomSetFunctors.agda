open import Library
open import Categories
open import Functors
open import Categories.ProductCat
open import Categories.Sets

module HomSetFunctors where

  HomC : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{L : Fun C D}{R : Fun D C} → Fun ((D Op) ×C C) Sets
  HomC {C = C}{D}{L}{R} = let open Cat
                              open Fun
                          in functor (λ { (Y , X) → Hom D (OMap L X) Y })
                                     (λ { (f , g) h → {!!} })
                                     {!!}
                                     {!!}

{-  homC : (f : Hom X X') → (g : Hom Y Y') → Hom
  homC : Fun (C Op ×C C) ?
  homC = ?
-}
