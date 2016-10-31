module Adjunctions where

open import Library
open import Categories
open import Functors

open Fun

record Adj {a b c d}(C : Cat {a}{b})(D : Cat {c}{d}) : Set (a ⊔ b ⊔ c ⊔ d)
  where
  constructor adjunction  
  open Cat C renaming (Obj to ObjC ; Hom to HomC ; _∙_ to _∙C_ )
  open Cat D renaming (Obj to ObjD ; Hom to HomD ; _∙_ to _∙D_ )
  field L        : Fun C D
        R        : Fun D C
        left     : {X : ObjC}{Y : ObjD} → 
                   HomD (OMap L X) Y → HomC X (OMap R Y)
        right    : {X : ObjC}{Y : ObjD} → 
                   HomC X (OMap R Y) → HomD (OMap L X) Y
        lawa     : {X : ObjC}{Y : ObjD}(f : HomD (OMap L X) Y) → 
                   right (left f) ≅ f
        lawb     : {X : ObjC}{Y : ObjD}(f : HomC X (OMap R Y)) →
                   left (right f) ≅ f
        natleft  : {X X' : ObjC}{Y Y' : ObjD}
                   (f : HomC X' X)(g : HomD Y Y')
                   (h : HomD (OMap L X) Y) → 
                   HMap R g ∙C left h ∙C f  ≅ left (g ∙D h ∙D HMap L f) 
        natright : {X X' : ObjC}{Y Y' : ObjD}
                   (f : HomC X' X)(g : HomD Y Y')
                   (h : HomC X (OMap R Y)) → 
                   right (HMap R g ∙C h ∙C f) ≅  g ∙D (right h ∙D HMap L f) 

open import Naturals

record Adj2 {a b c d}(C : Cat {a}{b})(D : Cat {c}{d}) : Set (a ⊔ b ⊔ c ⊔ d)
  where
  constructor adjunction2  
  open Cat C renaming (Obj to ObjC ; Hom to HomC ; _∙_ to _∙C_ )
  open Cat D renaming (Obj to ObjD ; Hom to HomD ; _∙_ to _∙D_ )
  field L         : Fun C D
        R         : Fun D C
        η         : NatT IdF (R ○ L)
        ε         : NatT (L ○ R) IdF 
        triangle1 : compVNat {F = IdF ○ R}{G = (R ○ L) ○ R}{H = R ○ IdF} {!(compFNat R ε)!} (compNatF η R) ≅ idNat {F = R}
        triangle2 : {!compNatF η R!}
-- lemma : Adj C D -> Adj2 C D

-- lemma2 : Adj2 C D -> Adj C D

-- probar que ir de Adj en Adj2 y luego de Adj2 en Adj hace que vuelva al mismo elemento (lemma2 (lemma x) = x, lemma (lemma2 x) = x)


--Usar una compVNat más general, que no necesite que G sea igual