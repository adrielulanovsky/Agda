module Naturals where

open import Library
open import Categories
open import Functors

open Fun

record NatT {a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}(F G : Fun C D) : Set (a ⊔ b ⊔ d) where
  constructor natural
  open Cat
  field cmp : ∀ {X} → Hom D (OMap F X) (OMap G X)
        nat : ∀{X Y}{f : Hom C X Y} → 
              _∙_ D (HMap G f) cmp ≅ _∙_ D cmp (HMap F f)

-- Dos transformaciones naturales son iguales si sus componentes son iguales.
NatTEq : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F G : Fun C D}
         {α β : NatT F G} → 
         (λ {X} → NatT.cmp α {X}) ≅ (λ {X} → NatT.cmp β {X}) → 
         α ≅ β
NatTEq {α = natural cmp _} {natural .cmp _} refl =
  cong (natural cmp) (iext λ _ → iext λ _ → iext λ _ → ir _ _)

-- NatTEq2 se puede usar cuando los funtores intervinientes no son definicionalmente iguales
NatTEq2 : ∀ {a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F G F' G' : Fun C D}
            {α : NatT F G}{β : NatT F' G'}
          → F ≅ F' → G ≅ G'  
          → (λ {X} → NatT.cmp α {X}) ≅ (λ {X} → NatT.cmp β {X})
          → α ≅ β
NatTEq2 {α = natural cmp _} {natural .cmp _} refl refl refl =
  cong (natural cmp) (iext λ _ → iext λ _ → iext λ _ → ir _ _)

--------------------------------------------------
-- la identidad es una transformación natural
idNat : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F : Fun C D} → NatT F F
idNat {D = D}{F} = let open Cat D in natural iden (λ {X}{Y}{f} -> 
                   proof
                   HMap F f ∙ iden
                   ≅⟨ idr ⟩
                   HMap F f
                   ≅⟨ sym idl ⟩
                   iden ∙ HMap F f
                   ∎)

-- Composición (vertical) de transformaciones naturales
compVNat : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F G H : Fun C D} → 
          NatT G H → NatT F G → NatT F H
compVNat {D = D}{F}{G}{H} b a = let open Cat D; open NatT in
                                natural ((cmp b) ∙ (cmp a))
                                        (λ {X}{Y}{f} -> 
                proof
                HMap H f ∙ (cmp b ∙ cmp a)
                ≅⟨ sym ass ⟩
                (HMap H f ∙ cmp b) ∙ cmp a
                ≅⟨ cong (λ x -> x ∙ cmp a) (nat b) ⟩
                (cmp b ∙ HMap G f) ∙ cmp a
                ≅⟨ ass ⟩
                cmp b ∙ (HMap G f ∙ cmp a)
                ≅⟨ cong ((_∙_) (cmp b)) (nat a) ⟩
                cmp b ∙ (cmp a ∙ HMap F f)
                ≅⟨ sym ass ⟩
                (cmp b ∙ cmp a) ∙ HMap F f
                ∎ )

--------------------------------------------------
{- Categorías de funtores
 Dadas dos categorías C y D, los objetos son los funtores : C → D,
 y los morfismos son las transformaciones naturales entre ellos.
-}
FunctorCat-id : ∀{a b c d} → {C : Cat {a}{b}} → {D : Cat {c}{d} } → {F G : Fun C D} -> (f : NatT F G) → compVNat idNat f ≅ f
FunctorCat-id {D = D} a = let open NatT
                              open Cat D
{-                          in proof
                              (compVNat idNat a)
                              ≅⟨ {!!} ⟩
                              {!!}
                              ≅⟨ {!!} ⟩
                              a
                              ∎-}
                            in NatTEq {!proof
                               cmp (compVNat idNat a)
                               ≅⟨ ? ⟩
                               cmp a
                               ∎!}
                               

FunctorCat : ∀{a b c d} → Cat {a}{b} → Cat {c}{d} → Cat
FunctorCat C D = record{
  Obj  = Fun C D;
  Hom  = NatT;
  iden = idNat;
  _∙_  = compVNat;
  idl  = {!!};
  idr  = {!!};
  ass  = {!!}}

--------------------------------------------------
-- Algunos ejemplos de transformaciones naturales

module Ejemplos where

 open import Categories.Sets
 open import Functors.List
 open import Functors.Maybe
 open import Functors.Constant
 open import Data.Nat

 {- reverse es una transformación natural -}

 open Cat (Sets {lzero})

 --
 revNat-proof : {X Y : Obj} {f : Hom X Y}(a : List X) →
      (HMap ListF f ∙ reverse) a ≅ (reverse ∙ HMap ListF f) a
 revNat-proof [] = refl
 revNat-proof {f = f} (x ∷ xs) = {!!}{-proof
                      (HMap ListF f ∙ reverse) (x ∷ xs)
                      ≅⟨ {!!} ⟩
                      {!map f ((reverse xs) ++ (x ∷ []))!}
                      ≅⟨ {!!} ⟩
                      {!!}
                      ≅⟨ {!!} ⟩
                      (reverse ∙ HMap ListF f) (x ∷ xs)
                      ∎-}

 revNat : NatT ListF ListF
 revNat = natural reverse {!!}

 --
 concatNat : NatT (ListF ○ ListF) ListF
 concatNat = natural concat {!!}

 --
{- lengthNat-proof : {X Y : Obj} {f : Hom X Y} →
      (HMap (K ℕ) f) ∙ length ≅ length ∙ HMap ListF f
 lengthNat-proof = {!_∙_!}
-}

 lengthNat : NatT ListF (K ℕ)
 lengthNat = natural length (ext {!HMap (K ℕ) !})

 --
 safeHead : {A : Set} → List A → Maybe A
 safeHead [] = nothing
 safeHead (x ∷ xs) = just x

 headNat-proof : {X Y : Obj} {f : Hom X Y}(xs : List X) →
      (HMap MaybeF f ∙ safeHead) xs ≅ (safeHead ∙ HMap ListF f) xs
 headNat-proof [] = refl
 headNat-proof (x ∷ xs) = refl

 headNat : NatT ListF MaybeF
 headNat = natural safeHead (ext headNat-proof)

 --
--------------------------------------------------
-- Natural isomorphism
{- Un isomorfismo natural es una transformación natural tal que
   cada componente es un isomorfismo. -}
open import Categories.Iso

record NatIso {a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}
             {F G : Fun C D}(η : NatT F G)  : Set (a ⊔ d) where
  constructor natiso
  field cmpIso : ∀{X} -> Iso D (NatT.cmp η {X})


--------------------------------------------------
-- composición con funtor (a izquierda y a derecha)

compFNat : ∀{a b c d e f}{C : Cat {a} {b}}{D : Cat {c} {d}}{E : Cat {e} {f}}
            {F G : Fun C D}
         → (J : Fun D E)
         → (η : NatT F G) → NatT (J ○ F) (J ○ G)
compFNat {D = D} {E} {F} {G} J η =
               let open NatT η
                   open Cat D renaming (_∙_ to _∙D_)
                   open Cat E renaming (_∙_ to _∙E_)
               in
               {!!}

compNatF :  ∀{a b c d e f}{C : Cat {a} {b}}{D : Cat {c} {d}}{E : Cat {e} {f}}
            {J K : Fun D E}
         → (η : NatT J K)
         → (F : Fun C D)
         → NatT (J ○ F) (K ○ F)
compNatF {C = C} {D} {E} {J} {K} η F =
               let open NatT η
                   open Cat D renaming (_∙_ to _∙D_)
                   open Cat E renaming (_∙_ to _∙E_)
               in {!!}

--------------------------------------------------
-- Composición horizontal
compHNat : ∀{a b c d e f}{C : Cat {a} {b}}{D : Cat {c} {d}}{E : Cat {e} {f}}
            {F G : Fun C D}{J K : Fun D E}
            (η : NatT F G)(ε : NatT J K)
            → NatT (J ○ F) (K ○ G)
compHNat {G = G} {J} η ε = {!!}


-- La composición horizontal es asociativa
compHNat-assoc : ∀{a1 b1 a2 b2 a3 b3 a4 b4}
                    {C1 : Cat {a1} {b1}}{C2 : Cat {a2} {b2}}{C3 : Cat {a3} {b3}}{C4 : Cat {a4} {b4}}
                    {F G : Fun C1 C2}{J K : Fun C2 C3}{L M : Fun C3 C4} 
                 →  (η1 : NatT F G)(η2 : NatT J K)(η3 : NatT L M)
                 →  compHNat (compHNat η1 η2) η3 ≅ compHNat η1 (compHNat η2 η3)
compHNat-assoc {C3 = C3}{C4 = C4}{J = J}{L = L} (natural cmp1 _) (natural cmp2 _) (natural cmp3 _) =
                   let   _∙4_ = Cat._∙_ C4
                         _∙3_ = Cat._∙_ C3                         
                   in
                     {!!}


-- ley de intercambio
interchange : ∀{a b c d e f}{C : Cat {a} {b}}{D : Cat {c} {d}}{E : Cat {e} {f}}
               {F G H : Fun C D}{I J K : Fun D E}
              → (α : NatT F G) → (β : NatT G H)
              → (γ : NatT I J) → (δ : NatT J K)
              → compHNat (compVNat β α) (compVNat δ γ) ≅ compVNat (compHNat β δ) (compHNat α γ)
interchange {D = D}{E}{I = I}{J} (natural α _) (natural β _) (natural γ natγ) (natural δ _) =
          let open NatT
              _∙D_ = Cat._∙_ D
              open Cat E
           in
           {!!}


