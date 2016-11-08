open import Library
open import Categories
open import Functors
open import Naturals
open import Adjunctions
open import Adjunctions.Equality
open Fun


module AdjIso {a}{b}{c}{d}(C : Cat {a}{b})(D : Cat {c}{d}) where
  open NatT
  open Cat C renaming (Obj to ObjC ; Hom to HomC ; _∙_ to _∙C_ ; iden to idC ; idr to idrC ; idl to idlC ; ass to assC ; congl to conglC ; congr to congrC ; conglr to conglrC )
  open Cat D renaming (Obj to ObjD ; Hom to HomD ; _∙_ to _∙D_ ; iden to idD ; idr to idrD ; idl to idlD ; ass to assD ; congl to conglD ; congr to congrD ; conglr to conglrD)

  lemma1 : Adj C D -> Adj3 C D
  lemma1 (adjunction L R left right lawa lawb natleft natright) = 
         adjunction3 L 
                     R 
                     (left idD) 
                     (right idC) 
                     (λ {X}{Y}{f} ->
    proof
    HMap (R ○ L) f ∙C left idD
    ≅⟨ conglC refl ⟩
    HMap R (HMap L f) ∙C left idD
    ≅⟨ sym idrC ⟩
    (HMap R (HMap L f) ∙C left idD) ∙C idC
    ≅⟨ assC ⟩
    HMap R (HMap L f) ∙C left idD ∙C idC
    ≅⟨ natleft idC (HMap L f) idD ⟩
    left (HMap L f ∙D idD ∙D HMap L idC)
    ≅⟨ cong left (congrD idlD) ⟩
    left (HMap L f ∙D HMap L idC)
    ≅⟨ cong left (congrD (fid L)) ⟩
    left (HMap L f ∙D idD)
    ≅⟨ cong left idrD ⟩
    left (HMap L f)
    ≅⟨ cong left (sym idlD) ⟩
    left (idD ∙D HMap L f)
    ≅⟨ cong left (sym idlD) ⟩
    left (idD ∙D idD ∙D HMap L f)
    ≅⟨ sym (natleft f idD idD) ⟩
    HMap R idD ∙C left idD ∙C f
    ≅⟨ conglC (fid R) ⟩
    idC ∙C left idD ∙C f
    ≅⟨ idlC ⟩
    left idD ∙C f
    ≅⟨ congrC refl ⟩
    left idD ∙C HMap (IdF {C = C}) f
    ∎) 
                     (λ {X}{Y}{f} →
    proof
    HMap (IdF {C = D}) f ∙D right idC
    ≅⟨ conglD refl ⟩
    f ∙D right idC
    ≅⟨ sym idrD ⟩
    (f ∙D right idC) ∙D idD
    ≅⟨ congrD (sym (fid L)) ⟩
    (f ∙D right idC) ∙D HMap L idC
    ≅⟨ assD ⟩
    f ∙D right idC ∙D HMap L idC
    ≅⟨ sym (natright idC f idC) ⟩
    right (HMap R f ∙C idC ∙C idC)
    ≅⟨ cong right (congrC idlC) ⟩
    right (HMap R f ∙C idC)
    ≅⟨ cong right idrC ⟩
    right (HMap R f)
    ≅⟨ cong right (sym idlC) ⟩
    right (idC ∙C HMap R f)
    ≅⟨ cong right (conglC (sym (fid R))) ⟩
    right (HMap R idD ∙C HMap R f)
    ≅⟨ cong right (congrC (sym idlC)) ⟩
    right (HMap R idD ∙C idC ∙C HMap R f)
    ≅⟨ natright (HMap R f) idD idC ⟩
    idD ∙D right idC ∙D HMap (L ○ R) f
    ≅⟨ idlD ⟩
    right idC ∙D HMap (L ○ R) f
    ∎) 
                     (proof
   HMap R (right idC) ∙C left idD
   ≅⟨ sym (congrC idrC) ⟩
   HMap R (right idC) ∙C left idD ∙C idC
   ≅⟨ natleft idC (right idC) idD ⟩
   left (right idC ∙D idD ∙D HMap L idC)
   ≅⟨ cong left (congrD idlD) ⟩
   left (right idC ∙D HMap L idC)
   ≅⟨ cong left (congrD (fid L)) ⟩
   left (right idC ∙D idD)
   ≅⟨ cong left idrD ⟩
   left (right idC)
   ≅⟨ lawb idC ⟩
   idC
   ∎) 
                     (proof
   right idC ∙D HMap L (left idD)
   ≅⟨ sym idlD ⟩
   idD ∙D right idC ∙D HMap L (left idD)
   ≅⟨ sym (natright (left idD) idD idC) ⟩
   right (HMap R idD ∙C idC ∙C left idD)
   ≅⟨ cong right (congrC idlC) ⟩
   right (HMap R idD ∙C left idD)
   ≅⟨ cong right (conglC (fid R)) ⟩
   right (idC ∙C left idD)
   ≅⟨ cong right idlC ⟩
   right (left idD)
   ≅⟨ lawa idD ⟩
   idD
   ∎)

  lemma2 : Adj3 C D -> Adj C D
  lemma2 (adjunction3 L R η ε η-nat ε-nat triangle1 triangle2) = 
         adjunction L 
                    R 
                    (λ f → HMap R f ∙C η) 
                    (λ g → ε ∙D HMap L g) 
                    (λ f → proof
   ε ∙D HMap L (HMap R f ∙C η)
   ≅⟨ congrD (fcomp L) ⟩
   ε ∙D HMap L (HMap R f) ∙D HMap L η
   ≅⟨ sym assD ⟩
   (ε ∙D HMap L (HMap R f)) ∙D HMap L η
   ≅⟨ conglD (sym ε-nat) ⟩
   (f ∙D ε) ∙D HMap L η
   ≅⟨ assD ⟩
   f ∙D ε ∙D HMap L η
   ≅⟨ congrD triangle2 ⟩
   f ∙D idD
   ≅⟨ idrD ⟩
   f
   ∎) 
                    (λ f → proof
   HMap R (ε ∙D HMap L f) ∙C η
   ≅⟨ conglC (fcomp R) ⟩
   (HMap R ε ∙C HMap R (HMap L f)) ∙C η
   ≅⟨ assC ⟩
   HMap R ε ∙C HMap R (HMap L f) ∙C η
   ≅⟨ congrC η-nat ⟩
   HMap R ε ∙C η ∙C f
   ≅⟨ sym assC ⟩
   (HMap R ε ∙C η) ∙C f
   ≅⟨ conglC triangle1 ⟩
   idC ∙C f
   ≅⟨ idlC ⟩
   f
   ∎) 
                    (λ f g h → proof
   HMap R g ∙C (HMap R h ∙C η) ∙C f
   ≅⟨ congrC assC ⟩
   HMap R g ∙C HMap R h ∙C η ∙C f
   ≅⟨ congrC (congrC (sym η-nat)) ⟩
   HMap R g ∙C HMap R h ∙C HMap R (HMap L f) ∙C η
   ≅⟨ congrC (sym assC) ⟩
   HMap R g ∙C (HMap R h ∙C HMap R (HMap L f)) ∙C η
   ≅⟨ sym assC ⟩
   (HMap R g ∙C HMap R h ∙C HMap R (HMap L f)) ∙C η
   ≅⟨ conglC (sym (congrC (fcomp R))) ⟩
   (HMap R g ∙C HMap R (h ∙D HMap L f)) ∙C η
   ≅⟨ sym (conglC (fcomp R)) ⟩
   HMap R (g ∙D h ∙D HMap L f) ∙C η
   ∎) 
                    (λ f g h → proof
   ε ∙D HMap L (HMap R g ∙C h ∙C f)
   ≅⟨ congrD (fcomp L) ⟩
   ε ∙D HMap L (HMap R g) ∙D HMap L (h ∙C f)
   ≅⟨ sym assD ⟩
   (ε ∙D HMap L (HMap R g)) ∙D HMap L (h ∙C f)
   ≅⟨ conglD (sym ε-nat) ⟩
   (g ∙D ε) ∙D HMap L (h ∙C f)
   ≅⟨ congrD (fcomp L) ⟩
   (g ∙D ε) ∙D HMap L h ∙D HMap L f
   ≅⟨ sym assD ⟩
   ((g ∙D ε) ∙D HMap L h) ∙D HMap L f
   ≅⟨ conglD assD ⟩
   (g ∙D ε ∙D HMap L h) ∙D HMap L f
   ≅⟨ assD ⟩
   g ∙D (ε ∙D HMap L h) ∙D HMap L f
   ∎)  

  lemma3 : ∀{A} -> lemma2 (lemma1 A) ≅ A
  lemma3 {A} = let open Adj A
               in Adj-Eq (lemma2 (lemma1 A)) A refl refl (ext (λ a → proof
   HMap R a ∙C left idD
   ≅⟨ sym idrC ⟩
   (HMap R a ∙C left idD) ∙C idC
   ≅⟨ assC ⟩
   HMap R a ∙C left idD ∙C idC
   ≅⟨ natleft idC a idD ⟩
   left (a ∙D idD ∙D HMap L idC)
   ≅⟨ cong left (congrD idlD) ⟩
   left (a ∙D HMap L idC)
   ≅⟨ cong left (congrD (fid L)) ⟩
   left (a ∙D idD)
   ≅⟨ cong left idrD ⟩
   left a
   ∎))

  lemma4 : ∀{A} -> lemma1 (lemma2 A) ≅ A
  lemma4 {A} = let open Adj3 A
               in {!!}
{-  lemma1 : Adj C D -> Adj2 C D
  lemma1 (adjunction L R left right lawa lawb natleft natright) =
                     adjunction2 L
                                 R
                                 (natural (left idD)
                                          (λ {X}{Y}{f} ->
    proof
    HMap (R ○ L) f ∙C left idD
    ≅⟨ conglC refl ⟩
    HMap R (HMap L f) ∙C left idD
    ≅⟨ sym idrC ⟩
    (HMap R (HMap L f) ∙C left idD) ∙C idC
    ≅⟨ assC ⟩
    HMap R (HMap L f) ∙C left idD ∙C idC
    ≅⟨ natleft idC (HMap L f) idD ⟩
    left (HMap L f ∙D idD ∙D HMap L idC)
    ≅⟨ cong left (congrD idlD) ⟩
    left (HMap L f ∙D HMap L idC)
    ≅⟨ cong left (congrD (fid L)) ⟩
    left (HMap L f ∙D idD)
    ≅⟨ cong left idrD ⟩
    left (HMap L f)
    ≅⟨ cong left (sym idlD) ⟩
    left (idD ∙D HMap L f)
    ≅⟨ cong left (sym idlD) ⟩
    left (idD ∙D idD ∙D HMap L f)
    ≅⟨ sym (natleft f idD idD) ⟩
    HMap R idD ∙C left idD ∙C f
    ≅⟨ conglC (fid R) ⟩
    idC ∙C left idD ∙C f
    ≅⟨ idlC ⟩
    left idD ∙C f
    ≅⟨ congrC refl ⟩
    left idD ∙C HMap (IdF {C = C}) f
    ∎
                                          ))
                                 (natural (right idC)
                                          (λ {X}{Y}{f} →
    proof
    HMap (IdF {C = D}) f ∙D right idC
    ≅⟨ conglD refl ⟩
    f ∙D right idC
    ≅⟨ sym idrD ⟩
    (f ∙D right idC) ∙D idD
    ≅⟨ congrD (sym (fid L)) ⟩
    (f ∙D right idC) ∙D HMap L idC
    ≅⟨ assD ⟩
    f ∙D right idC ∙D HMap L idC
    ≅⟨ sym (natright idC f idC) ⟩
    right (HMap R f ∙C idC ∙C idC)
    ≅⟨ cong right (congrC idlC) ⟩
    right (HMap R f ∙C idC)
    ≅⟨ cong right idrC ⟩
    right (HMap R f)
    ≅⟨ cong right (sym idlC) ⟩
    right (idC ∙C HMap R f)
    ≅⟨ cong right (conglC (sym (fid R))) ⟩
    right (HMap R idD ∙C HMap R f)
    ≅⟨ cong right (congrC (sym idlC)) ⟩
    right (HMap R idD ∙C idC ∙C HMap R f)
    ≅⟨ natright (HMap R f) idD idC ⟩
    idD ∙D right idC ∙D HMap (L ○ R) f
    ≅⟨ idlD ⟩
    right idC ∙D HMap (L ○ R) f
    ∎)
                                          )
                                 (NatTEq2 ○-idl ○-idr ({!Adj2.η!} {-proof
   cmp
     (compVNat2
      (compFNat R
       (natural (right idC)
        _))
      (compNatF
       (natural (left idD)
        _)
       R)
      _)
   ≅⟨ {!!} ⟩
   {!!}
   ≅⟨ {!!} ⟩
   {!!}
   ≅⟨ {!!} ⟩
   {!!}
   ≅⟨ {!!} ⟩
   {!!}
   ≅⟨ {!!} ⟩
   {!!}
   ≅⟨ {!!} ⟩
   {!!}
   ≅⟨ {!!} ⟩
   left (right idC)
   ≅⟨ lawb idC ⟩
   idC
   ≅⟨ refl ⟩
   cmp idNat
   ∎ -}))
                                 {!!}

  lemma2 : Adj2 C D -> Adj C D
  lemma2 (adjunction2 L R η ε triangle1 triangle2) =
         adjunction L 
                    R 
                    (λ f → HMap R f ∙C NatT.cmp η ) 
                    (λ g → NatT.cmp ε ∙D HMap L g) 
                    (λ f → proof
   cmp ε ∙D HMap L (HMap R f ∙C cmp η)
   ≅⟨ sym {!nat ε {f = ?}!} ⟩
   {!NatT.nat η!}
   ≅⟨ {!!} ⟩
   {!!}
   ≅⟨ {!!} ⟩
   {!!}
   ≅⟨ {!!} ⟩
   {!!}
   ≅⟨ {!!} ⟩
   {!!}
   ≅⟨ {!!} ⟩
   {!!}
   ≅⟨ {!!} ⟩
   {!!}
   ≅⟨ {!!} ⟩
   {!!}
   ≅⟨ {!!} ⟩
   f
   ∎) 
                    {!NatT.cmp ε!} 
                    {!!} 
                    {!NatT.cmp (compNatF ε L)!}

-}  
{-
  lemma3 : Adj2 C D → Adj3 C D
  lemma3 (adjunction2 L R η ε triangle1 triangle2) = 
         adjunction3 L 
                     R 
                     (NatT.cmp η) 
                     (NatT.cmp ε) 
                     (NatT.nat η) 
                     (NatT.nat ε) 
                     {!!} 
                     {!!}

  lemma4 : Adj3 C D → Adj2 C D
  lemma4 (adjunction3 L R eta epsilon eta-nat eps-nat triangle1 triangle2) = 
         adjunction2 L 
                     R 
                     (natural eta eta-nat) 
                     (natural epsilon eps-nat) 
                     (NatTEq2 ○-idl ○-idr (λ {X} -> proof
   cmp
     (compVNat2
      (compFNat R
       (natural epsilon eps-nat))
      (compNatF (natural eta eta-nat) R)
      ○-assoc)
   ≅⟨ {!!} ⟩
   HMap R epsilon ∙C eta
   ≅⟨ triangle1 ⟩
   idC
   ≅⟨ refl ⟩
   cmp idNat {C = C} 
   ∎)) 
                     (NatTEq2 ○-idr ○-idl {!triangle2!})
-}

-- probar que ir de Adj en Adj2 y luego de Adj2 en Adj hace que vuelva al mismo elemento (lemma2 (lemma x) = x, lemma (lemma2 x) = x)


--Usar una compVNat más general, que no necesite que G sea igual

{-
compNatF ε L : {X : ObjC} → HomD (OMap ((L ○ R) ○ L) X) (OMap (IdF ○ L) X)
compFNat R ε : HomC (OMap (R ○ (L ○ R)) X) (OMap R X)
compNatF η R : {X : ObjD} → HomC (OMap (IdF ○ R) X) (OMap ((R ○ L) ○ R) X)
compFNat L η : HomD (OMap L X) (OMap (L ○ (R ○ L)) X)

proof
   ?
   ≅⟨ ? ⟩
   ?
   ≅⟨ ? ⟩
   ?
   ≅⟨ ? ⟩
   ?
   ≅⟨ ? ⟩
   ?
   ≅⟨ ? ⟩
   ?
   ≅⟨ ? ⟩
   ?
   ≅⟨ ? ⟩
   ?
   ≅⟨ ? ⟩
   ?
   ≅⟨ ? ⟩
   ?
   ∎



-}
