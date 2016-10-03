open import Categories

module Construcciones2 where

open import Library hiding (_×_ ; swap; _+_)

open import Categories.Products
open import Categories.Terminal
open import Categories.Iso
open import Categories.Initial
open import Categories.Coproducts
open import Construcciones

--------------------------------------------------

module SetsStructure {l : Level} where

 open import Categories.Sets

 {- Probar que la categoría Sets tiene objeto inicial y coproductos -}
 ZeroSet : Initial Sets ⊥
 ZeroSet = init (λ { () }) (ext (λ{ () }))

 data Either {a b}(A : Set a)(B : Set b) : Set (a ⊔ b) where
   left : A -> Either A B
   right : B -> Either A B
 
 SetsHasCoproducts : ∀{l} → Coproducts (Sets {l})
 SetsHasCoproducts = coproduct (λ A B → Either A B) left right (λ f g → λ {(left x) → f x ; (right x) -> g x}) refl refl (λ p q → ext (λ { (left x) → cong-app p x ; (right x) → cong-app q x }))

--------------------------------------------------
module InitialIso {a}{b}(C : Cat {a}{b}) where

 open Cat C
 open Initial

 {- el morfismo universal del objeto inicial a sí mismo es la identidad -}

 init-iden : (I : Obj){init : Initial C I}
           → i init {I} ≅ iden {I}
 init-iden I {initial} = law initial


--------------------------------------------------
 {- Probar que un objeto terminal es inicial en la categoría dual y viceversa -}
 open Terminal renaming (law to lawt)
 TerminalInitialDuality : {X : Obj} → Terminal C X → Initial (C Op) X
 TerminalInitialDuality terminal = init (t terminal) (lawt terminal)

 InitialTerminalDuality : {X : Obj} → Initial C X → Terminal (C Op) X
 InitialTerminalDuality initial = term (i initial) (law initial)

--------------------------------------------------

 open TerminalIso
 
 {- Probar que dos objetos iniciales son necesariamente isomorfos *usando dualidad* -}
 InitialIso : (I I' : Obj)
            → (p : Initial C I)
            → (q : Initial C I')
            → Iso C (i p {I'})
 InitialIso I I' p q = iso-op (TerminalIso (C Op) I I' (InitialTerminalDuality p) (InitialTerminalDuality q))

--------------------------------------------------------
-- Probar que los coproductos son productos en la categoría dual
ProductCoproductDuality : ∀{a}{b}{C : Cat {a}{b}}
                        → Products C
                        → Coproducts (C Op)
ProductCoproductDuality (prod _×_ π₁ π₂ ⟨_,_⟩ law1 law2 law3) = 
                   coproduct (λ A B → A × B) π₁ π₂ ⟨_,_⟩ law1 law2 law3 

CoproductProductDuality : ∀{a}{b}{C : Cat {a}{b}}
                        → Coproducts C
                        → Products (C Op)
CoproductProductDuality (coproduct _+_ inl inr [_,_] law1 law2 law3) = 
                                   prod _+_ inl inr [_,_] law1 law2 law3

--------------------------------------------------
module CoproductIso {a}{b}(C : Cat {a}{b})  where

  open Coproducts

  open Cat C

  open ProductIso (C Op) renaming (ProductIso to piso)

  {- Probar que los coproductos son únicos hasta un isomorfismo *usando dualidad* -}
  CoproductIso : ∀{A B}(X Y : Coproducts C) → Iso C ([_,_] X {A} {B} (inl Y) (inr Y))
  CoproductIso X Y = iso-op (piso (CoproductProductDuality X) (CoproductProductDuality Y))

--------------------------------------------------

module CoproductMorphisms {a}{b}{C : Cat {a}{b}}{cp : Coproducts C} where

  open Cat C
  open Coproducts cp

  {- Definir el siguiente morfismo -}
  plus : ∀{A B C D}(f : Hom A B)(g : Hom C D) → Hom (A + C) (B + D)
  plus f g = [ inl ∙ f , inr ∙ g ]

  {- Probar las siguentes propiedades -}

  idplus : ∀{A B} → plus (iden {A}) (iden {B}) ≅ iden {A + B}
  idplus = sym (law3 (trans idl (sym idr)) (trans idl (sym idr)))

  idcomp :  ∀{A B C D E F}
         → (f : Hom B C)(g : Hom A B)
         → (h : Hom E F)(i : Hom D E)
         → plus (f ∙ g) (h ∙ i) ≅ plus f h ∙ plus g i
  idcomp  f g h i = proof
              plus (f ∙ g) (h ∙ i)
              ≅⟨ cong₂ [_,_] (sym ass) (sym ass) ⟩
              [ (inl ∙ f) ∙ g , (inr ∙ h) ∙ i ]
              ≅⟨ cong₂ (λ x y → [ x ∙ g , y ∙ i ]) (sym law1) (sym law2)  ⟩
              [ ((plus f h) ∙ inl) ∙ g , ((plus f h) ∙ inr) ∙ i ]
              ≅⟨ cong₂ [_,_] ass ass ⟩
              [ (plus f h) ∙ (inl ∙ g) , (plus f h) ∙ (inr ∙ i) ]
              ≅⟨ cong₂ (λ x y → [ (plus f h) ∙ x , (plus f h) ∙ y ]) (sym law1) (sym law2) ⟩
              [ (plus f h) ∙ (plus g i) ∙ inl , (plus f h) ∙ (plus g i) ∙ inr ]
              ≅⟨ cong₂ [_,_] (sym ass) (sym ass) ⟩
              [ ((plus f h) ∙ (plus g i)) ∙ inl , ((plus f h) ∙ (plus g i)) ∙ inr ]
              ≅⟨ sym (law3 refl refl) ⟩
              plus f h ∙ plus g i
              ∎

   {- Probar que _+_ junto con plus definen unFunctor C ×C C → C -}


module Intercambio {a}{b}{C : Cat {a}{b}}{cp : Coproducts C}{p : Products C} where

  open Cat C
  open Coproducts cp
  open Products p renaming (law1 to lawp1 ; law2 to lawp2 ; law3 to lawp3)


   {- intercambio entre poducto y coproducto -}

  intercambio : ∀{A B C D}
         → (f : Hom A C)(g : Hom B C)
         → (h : Hom A D)(k : Hom B D)
         → ⟨ [ f , g ] , [ h , k ] ⟩ ≅ [ ⟨ f , h ⟩ , ⟨ g , k ⟩ ]
  intercambio f g h i = proof
                         ⟨ [ f , g ] , [ h , i ] ⟩
                        ≅⟨ sym (lawp3 {!!} {!!}) ⟩
                         {!!}
                        ≅⟨ {!!} ⟩
                         {!!}
                        ≅⟨ {!!} ⟩
                         {!!}
                        ≅⟨ law3 {!!} {!!} ⟩
                         [ ⟨ f , h ⟩ , ⟨ g , i ⟩ ]
                        ∎
