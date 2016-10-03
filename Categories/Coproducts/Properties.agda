
open import Categories
open import Categories.Coproducts


module Categories.Coproducts.Properties {l m}{C : Cat {l}{m}}(c : Coproducts C) where

open import Library hiding (_+_)
open Cat C
open Coproducts c

copair : ∀{X Y Z W}(f : Hom X Z)(g : Hom Y W) → Hom (X + Y) (Z + W)
copair f g = [ inl ∙ f , inr ∙ g ]

iden-cop : ∀{A B} →  copair (iden {A}) (iden {B}) ≅ iden {A + B}
iden-cop = {!!}

comp-cop : ∀{A B C A' B' C'}{f : Hom B C}{g : Hom A B}{h : Hom B' C'}{i : Hom A' B'}
         → copair (f ∙ g) (h ∙ i) ≅ copair f h ∙ copair g i
comp-cop = {!!}

inl-cop : ∀{A B C}{f : Hom C A}{g : Hom C B} → copair f g ∙ inl ≅ inl {A} {B} ∙ f
inl-cop = {!!}

inr-cop : ∀{A B C}{f : Hom C A}{g : Hom C B} → copair f g ∙ inr ≅ inr {A} {B} ∙ g
inr-cop = {!!}

fusion-cop : ∀{A B C D E}{f : Hom A B}{g : Hom C D}{h : Hom B E}{i : Hom D E} 
          → [ h , i ] ∙ (copair f g) ≅ [ h ∙ f , i ∙ g ]
fusion-cop = ?



