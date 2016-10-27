open import Categories
open import Categories.Initial
import Functors.Algebra
open import Functors

module PropFAlgebras {a}{b}{C : Cat {a}{b}}
                           {F : Fun C C}
     where

open import Library hiding (_×_)
open import Naturals
open import Functors.Algebra F

open Cat C
open Fun F
open F-algebra
open F-homomorphism


--------------------------------------------------
-- Propiedades
--------------------------------------------------

iden-α : fold α ≅ iden {μF} 
iden-α = cong homo-base (univ {f = iden-homo})

fold-conmute : ∀{A}{f : Hom (OMap A) A} ->
               fold f ∙ α ≅ f ∙ HMap (fold f)
fold-conmute {A}{f} = homo-prop (init-homo {falgebra A f})

fold-caract :  ∀{A}{f : Hom (OMap A) A}{h : Hom μF A} ->
               h ∙ α ≅ f ∙ HMap h -> fold f ≅ h
fold-caract {f = f}{h} x = cong homo-base (univ {f = homo h x})

-- Fusion
fusion : ∀{A B}{f : Hom (OMap A) A}{g : Hom (OMap B) B}{h : Hom A B}
      → h ∙ f ≅ g ∙ HMap h → h ∙ fold f ≅ fold g
fusion {f = f}{g}{h} x = sym (fold-caract (proof
    (h ∙ fold f) ∙ α
    ≅⟨ ass ⟩
    h ∙ fold f ∙ α
    ≅⟨ congr fold-conmute ⟩
    h ∙ f ∙ HMap (fold f)
    ≅⟨ sym ass ⟩
    (h ∙ f) ∙ HMap (fold f)
    ≅⟨ congl x ⟩
    (g ∙ HMap h) ∙ HMap (fold f)
    ≅⟨ ass ⟩
    g ∙ HMap h ∙ HMap (fold f)
    ≅⟨ congr (sym fcomp) ⟩
    g ∙ HMap (h ∙ fold f)
    ∎))
--
isfold : ∀{A}{f : Hom μF A}{g : Hom A μF}
      → g ∙ f ≅ iden {μF} → Σ[ h ∈ Hom (OMap A) A ] (f ≅ fold h)
isfold {A}{f}{g} x = f ∙ α ∙ HMap g ,
                     sym (fold-caract (proof
    f ∙ α
    ≅⟨ sym idr ⟩
    (f ∙ α) ∙ iden
    ≅⟨ congr (sym fid) ⟩
    (f ∙ α) ∙ HMap iden
    ≅⟨ congr (cong HMap (sym x)) ⟩
    (f ∙ α) ∙ HMap (g ∙ f)
    ≅⟨ congr fcomp ⟩
    (f ∙ α) ∙ HMap g ∙ HMap f
    ≅⟨ sym ass ⟩
    ((f ∙ α) ∙ HMap g) ∙ HMap f
    ≅⟨ congl ass ⟩
    (f ∙ α ∙ HMap g) ∙ HMap f
    ∎))
--
roll : ∀{A B}{f : Hom B A}{g : Hom (OMap A) B}
     → fold (f ∙ g) ≅ f ∙ fold (g ∙ HMap f)
roll {f = f}{g} = fold-caract (proof
    (f ∙ fold (g ∙ HMap f)) ∙ α
    ≅⟨ ass ⟩
    f ∙ fold (g ∙ HMap f) ∙ α
    ≅⟨ congr fold-conmute ⟩
    f ∙ (g ∙ HMap f) ∙ HMap (fold (g ∙ HMap f))
    ≅⟨ sym ass ⟩
    (f ∙ g ∙ HMap f) ∙ HMap (fold (g ∙ HMap f))
    ≅⟨ congl (sym ass) ⟩
    ((f ∙ g) ∙ HMap f) ∙ HMap (fold (g ∙ HMap f))
    ≅⟨ ass ⟩
    (f ∙ g) ∙ HMap f ∙ HMap (fold (g ∙ HMap f))
    ≅⟨ congr (sym fcomp) ⟩
    (f ∙ g) ∙ HMap (f ∙ fold (g ∙ HMap f))
    ∎)

--------------------------------------------------
-- Propiedades de álgebras iniciales en categorías
-- con oroductos
--------------------------------------------------

open import Categories.Products

module ProductProperties (prod : Products C) where

--
-- Banana split
-- Nos permite transformar dos folds en uno solo
-- Ayuda : usar fusion de productos (fusionP)
 open Products prod
 open import Categories.Products.Properties prod renaming (fusion to fusionP)

 banana-split : ∀{A B}{f : Hom (OMap A) A}{g : Hom (OMap B) B}
             → ⟨ fold f , fold g ⟩ ≅ fold ⟨ f ∙ HMap π₁ , g ∙ HMap π₂ ⟩
 banana-split {f = f}{g} = sym (fold-caract (
   proof
    ⟨ fold f , fold g ⟩ ∙ α
    ≅⟨ fusionP ⟩
    ⟨ fold f ∙ α , fold g ∙ α ⟩
    ≅⟨ cong₂ ⟨_,_⟩ fold-conmute fold-conmute ⟩
    ⟨ f ∙ HMap (fold f) , g ∙ HMap (fold g) ⟩
    ≅⟨ cong₂ ⟨_,_⟩ (congr (cong HMap (sym law1))) ((congr (cong HMap (sym law2)))) ⟩
    ⟨ f ∙ HMap (π₁ ∙ ⟨ fold f , fold g ⟩) ,
      g ∙ HMap (π₂ ∙ ⟨ fold f , fold g ⟩) ⟩
    ≅⟨ cong₂ ⟨_,_⟩ (congr fcomp) (congr fcomp) ⟩
    ⟨ f ∙ HMap π₁ ∙ HMap ⟨ fold f , fold g ⟩ ,
      g ∙ HMap π₂ ∙ HMap ⟨ fold f , fold g ⟩ ⟩
    ≅⟨ cong₂ ⟨_,_⟩ (sym ass) (sym ass) ⟩
    ⟨ (f ∙ HMap π₁) ∙ HMap ⟨ fold f , fold g ⟩ ,
      (g ∙ HMap π₂) ∙ HMap ⟨ fold f , fold g ⟩ ⟩
    ≅⟨ sym fusionP ⟩
    ⟨ f ∙ HMap π₁ , g ∙ HMap π₂ ⟩ ∙ HMap ⟨ fold f , fold g ⟩
    ∎))
--
-- Recursion mutua
 mutua1 : ∀{A B}{f : Hom μF A}{g : Hom μF B}{h : Hom (OMap (A × B)) A}{k : Hom (OMap (A × B)) B} 
       → f ∙ α ≅ h ∙ HMap ⟨ f , g ⟩
       → g ∙ α ≅ k ∙ HMap ⟨ f , g ⟩
       → ⟨ f , g ⟩ ≅ fold ⟨ h , k ⟩
 mutua1 {f = f}{g}{h}{k} p q = sym (fold-caract (proof
    ⟨ f , g ⟩ ∙ α
    ≅⟨ fusionP ⟩
    ⟨ f ∙ α , g ∙ α ⟩
    ≅⟨ cong₂ ⟨_,_⟩ p q ⟩
    ⟨ h ∙ HMap ⟨ f , g ⟩ , k ∙ HMap ⟨ f , g ⟩ ⟩
    ≅⟨ sym fusionP ⟩
    ⟨ h , k ⟩ ∙ HMap ⟨ f , g ⟩
    ∎))

 mutua2 : ∀{A B}{f : Hom μF A}{g : Hom μF B}{h : Hom (OMap (A × B)) A}{k : Hom (OMap (A × B)) B} 
       → ⟨ f , g ⟩ ≅ fold ⟨ h , k ⟩
       → Library._×_ (f ∙ α ≅ h ∙ HMap ⟨ f , g ⟩) (g ∙ α ≅ k ∙ HMap ⟨ f , g ⟩)
 mutua2 {f = f}{g}{h}{k} p = (proof
    f ∙ α
    ≅⟨ sym law1 ⟩
    π₁ ∙ ⟨ f ∙ α , g ∙ α ⟩
    ≅⟨ congr (sym fusionP) ⟩
    π₁ ∙ ⟨ f , g ⟩ ∙ α
    ≅⟨ congr (congl p) ⟩
    π₁ ∙ fold ⟨ h , k ⟩ ∙ α
    ≅⟨ congr fold-conmute ⟩
    π₁ ∙ ⟨ h , k ⟩ ∙ HMap (fold ⟨ h , k ⟩)
    ≅⟨ sym ass ⟩
    (π₁ ∙ ⟨ h , k ⟩) ∙ HMap (fold ⟨ h , k ⟩)
    ≅⟨ congl law1 ⟩
    h ∙ HMap (fold ⟨ h , k ⟩)
    ≅⟨ congr (cong HMap (sym p)) ⟩
    h ∙ HMap ⟨ f , g ⟩
    ∎) ,
    (proof
    g ∙ α
    ≅⟨ sym law2 ⟩
    π₂ ∙ ⟨ f ∙ α , g ∙ α ⟩
    ≅⟨ congr (sym fusionP) ⟩
    π₂ ∙ ⟨ f , g ⟩ ∙ α
    ≅⟨ congr (congl p) ⟩
    π₂ ∙ fold ⟨ h , k ⟩ ∙ α
    ≅⟨ congr fold-conmute ⟩
    π₂ ∙ ⟨ h , k ⟩ ∙ HMap (fold ⟨ h , k ⟩)
    ≅⟨ sym ass ⟩
    (π₂ ∙ ⟨ h , k ⟩) ∙ HMap (fold ⟨ h , k ⟩)
    ≅⟨ congl law2 ⟩
    k ∙ HMap (fold ⟨ h , k ⟩)
    ≅⟨ congr (cong HMap (sym p)) ⟩
    k ∙ HMap ⟨ f , g ⟩
    ∎)
