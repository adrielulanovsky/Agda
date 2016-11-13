module Adjunctions where

open import Library
open import Categories
open import Functors

open Fun

--Definición: Adjunciones Hom-Set
---- Dos functores L y R
---- Un isomorfismo natural left (con inversa right)

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

-------------------------
{- Definición: Adjunción Unit-Counit
---- Dos functores L y R
---- Dos transformaciones naturales:
-------- η : IdF → R ○ L  (unit)
-------- ε : L ○ R → IdF (counit)
---- que cumplen:
----------------- R ε ∘ η R ≅ idenC
----------------- ε L ∘ L η ≅ idenD
-}
record AdjUC {a b c d}(C : Cat {a}{b})(D : Cat {c}{d}) : Set (a ⊔ b ⊔ c ⊔ d)
  where
  constructor adjunctionUC  
  open Cat C renaming (Obj to ObjC ; Hom to HomC ; _∙_ to _∙C_ )
  open Cat D renaming (Obj to ObjD ; Hom to HomD ; _∙_ to _∙D_ )
  field L           : Fun C D
        R           : Fun D C
        η           : {X : ObjC} → HomC X (OMap (R ○ L) X) 
        ε           : {X : ObjD} → HomD (OMap (L ○ R) X) X
        η-nat       : {X Y : ObjC} {f : HomC X Y} →
                      (HMap (R ○ L) f) ∙C η ≅ η ∙C f
        ε-nat       : {X Y : ObjD} {f : HomD X Y} →
                      f ∙D ε ≅ ε ∙D HMap (L ○ R) f 
        triangle1   : {X : ObjD} → 
                      HMap R ε ∙C η {OMap R X} ≅ Cat.iden C {OMap R X}
        triangle2   : {X : ObjC} → 
                      ε {OMap L X} ∙D HMap L η ≅ Cat.iden D {OMap L X}

-------------------------

{-
record Adj2 {a b c d}(C : Cat {a}{b})(D : Cat {c}{d}) : Set (a ⊔ b ⊔ c ⊔ d)
  where
  constructor adjunction2  
  open Cat C renaming (Obj to ObjC ; Hom to HomC ; _∙_ to _∙C_ )
  open Cat D renaming (Obj to ObjD ; Hom to HomD ; _∙_ to _∙D_ )
  field L         : Fun C D
        R         : Fun D C
        η         : NatT IdF (R ○ L)
        ε         : NatT (L ○ R) IdF 
        triangle1 : compVNat2 (compFNat R ε) (compNatF η R) (○-assoc {F = R}{L}{R}) ≅ idNat {F = R}
        triangle2 : compVNat2 (compNatF ε L) (compFNat L η) (sym (○-assoc {F = L}{R}{L})) ≅ idNat {F = L}
-}


{-
compNatF ε L : {X : ObjC} → HomD (OMap ((L ○ R) ○ L) X) (OMap L X)
compFNat R ε : HomC (OMap (R ○ (L ○ R)) X) (OMap R X)
compNatF η R : {X : ObjD} → HomC (OMap R X) (OMap ((R ○ L) ○ R) X)
compFNat L η : HomD (OMap L X) (OMap (L ○ (R ○ L)) X)

-}
