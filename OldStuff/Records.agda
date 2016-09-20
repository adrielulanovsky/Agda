
module Records where

open import Relation.Binary.HeterogeneousEquality

postulate ext : ∀{a b}{A : Set a}{B B' : A → Set b}
                {f : ∀ a → B a}{g : ∀ a → B' a} → 
                (∀ a → f a ≅ g a) → f ≅ g


{- Veremos, el uso de records para definir estructuras algebraicas -}

{- Notar el uso de de Set₁ en lugar de Set ya que tenemos que
 situarnos en el nivel siguiente a Set₀ = Set, para hablar de cosas en
 Set (como carrier).

Los subindices son ₀ = \_0 y ₁ = \_1

 -}


record Monoid : Set₁  where
  infixr 7 _∙_
  field  Carrier : Set
         _∙_     : Carrier → Carrier → Carrier  {- ∙ = \. -}
         ε       : Carrier
         lid     : {x : Carrier} → ε ∙ x ≅ x
         rid     : {x : Carrier} → x ∙ ε ≅ x
         assoc   : {x y z : Carrier} → (x ∙ y) ∙ z ≅ x ∙ (y ∙ z) 

{- ¿Qué sucede si queremos usar un Carrier en Set₁? ¿o en Set₂? -}


open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties.Simple
{- propiedades simples de la suma, como por ejemplo
 +-right-identity, y +-assoc
-}

-- Monoide de Naturales y suma

module NatMonoid where

  NatMonoid : Monoid
  NatMonoid = record
                { Carrier = ℕ
                ; _∙_ = _+_
                ; ε = 0
                ; lid = refl
                ; rid = λ{x} → ≡-to-≅ (+-right-identity x)
                ; assoc = λ {x} {y} {z} → ≡-to-≅ (+-assoc x y z) }

{- ≡-to-≅ convierte igualdad proposicional en heterogénea -}

open NatMonoid

--------------------------------------------------
{- Ejercicio: Probar que las listas son un monoide -}

open ≅-Reasoning renaming (begin_ to proof_)

data List (A : Set) : Set where
   [] : List A
   _∷_ : (x : A) → (xs : List A) → List A

infixl 5 _∷_

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ y = y
(x ∷ xs) ++ y = x ∷ (xs ++ y)

ridlist : {X : Set} -> (x : List X) -> x ++ [] ≅ x
ridlist [] = refl
ridlist (x ∷ xs) = proof
   x ∷ xs ++ []
   ≅⟨ refl ⟩
   x ∷ (xs ++ [])
   ≅⟨ cong₂ _∷_ refl (ridlist xs) ⟩
   x ∷ xs
   ∎

assoclist : {X : Set} -> (x y z : List X) -> (x ++ y) ++ z ≅ x ++ (y ++ z)
assoclist [] y z = refl
assoclist (x ∷ xs) y z = proof
    (((x ∷ xs) ++ y) ++ z)
    ≅⟨ refl ⟩
    x ∷ (xs ++ y) ++ z
    ≅⟨ refl ⟩
    x ∷ ((xs ++ y) ++ z)
    ≅⟨ cong₂ _∷_ refl (assoclist xs y z) ⟩   
    ((x ∷ xs) ++ (y ++ z))
    ∎

-- Monoide de listas
ListMonoid : Set → Monoid
ListMonoid X = record
                 { Carrier = List X
                 ; _∙_ = _++_
                 ; ε = []
                 ; lid = refl
                 ; rid = \{x} -> ridlist x
                 ; assoc = \{x y z} -> assoclist x y z }

--------------------------------------------------

{- Ejercicio: Probar que para todo monoide M, N, el producto
   cartesiano de los respectivos soportes (Carrier M × Carrier N)
   es  el soporte de un monoide

 Ayuda : puede ser útil cong₂
-}
-- _×_ : {A B : Set} -> A -> B -> 
--data Cart (A B : Set) : Set where
--    _×_ : A -> B -> Cart A B

module CartProduct where
  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      proy1 : A
      proy2 : B

  infixl 5 _×_
  open _×_

  proy-is-cart : {A B : Set} -> (x : A × B) -> proy1 x , proy2 x ≅ x
  proy-is-cart (x1 , x2) = refl

  module CartesianMonoid (M N : Monoid) where
    open Monoid M renaming (Carrier to CarrierM; ε to ε1 ;  _∙_ to _∙1_; lid to lid1; rid to rid1; assoc to assoc1)
    open Monoid N renaming (Carrier to CarrierN; ε to ε2 ;  _∙_ to _∙2_; lid to lid2; rid to rid2; assoc to assoc2)
  
    _**_ : (CarrierM) × CarrierN ->  CarrierM × CarrierN ->  CarrierM × CarrierN
    _**_ (m1 , n1) (m2 , n2) = (m1 ∙1 m2)  , (n1 ∙2 n2)

    lidcartesian : (x : CarrierM × CarrierN) -> (ε1 , ε2) ** x ≅ x 
    lidcartesian (x1 , x2) =
                     proof
                     (ε1 , ε2) ** (x1 , x2)
                     ≅⟨ refl ⟩
                     (ε1 ∙1 x1) , (ε2 ∙2 x2)
                     ≅⟨ cong₂ _,_ lid1 lid2 ⟩
                     (x1 , x2)
                     ∎

    ridcartesian : (x : CarrierM × CarrierN) -> x ** (ε1 , ε2) ≅ x 
    ridcartesian (x1 , x2) =
                     proof
                     (x1 , x2) ** (ε1 , ε2)
                     ≅⟨ refl ⟩
                     (x1 ∙1 ε1) , (x2 ∙2 ε2)
                     ≅⟨ cong₂ _,_ rid1 rid2 ⟩
                     (x1 , x2)
                     ∎

    assoccartesian : (x y z : CarrierM × CarrierN) -> (x ** y) ** z ≅ x ** (y ** z) 
    assoccartesian (x1 , x2) (y1 , y2) (z1 , z2) = 
                     proof
                     ((x1 ∙1 y1) ∙1 z1) , ((x2 ∙2 y2) ∙2 z2)
                     ≅⟨ cong₂ _,_ assoc1 assoc2 ⟩
                     (x1 ∙1 y1 ∙1 z1) , (x2 ∙2 y2 ∙2 z2)
                     ∎


    CartesianMonoid : Monoid
    CartesianMonoid = 
             record
             { Carrier = CarrierM × CarrierN
             ; _∙_ = _**_
             ; ε = ε1 , ε2
             ; lid = \{x} -> lidcartesian x
             ; rid = \{x} -> ridcartesian x
             ; assoc = \{x} {y} {z} -> assoccartesian x y z  }




--------------------------------------------------
open import Function

-- Monoide de endofunciones
EndoMonoid : Set → Monoid
EndoMonoid X = record
                 { Carrier = X → X
                 ; _∙_ = _∘′_
                 ; ε = id
                 ; lid = refl
                 ; rid = refl
                 ; assoc = refl }


module Cayley where

  open Monoid using (Carrier)

  Cayley : Monoid → Monoid
  Cayley M = EndoMonoid (Carrier M) 

  rep : (M : Monoid) → Carrier M → Carrier (Cayley M)
  rep M x = λ y → x ∙ y
           where open Monoid M

  abs : (M : Monoid) → Carrier (Cayley M) → Carrier M
  abs M f = f ε
           where open Monoid M

  lemma : (M : Monoid) → {x : Carrier M} →
          abs M (rep M x) ≅ x
  lemma M = rid
           where open Monoid M

module Monoid-Homomorphism where
 open Monoid

-- Homomorfismos de monoides
 record Is-Monoid-Homo {M N : Monoid}(morph : Carrier M → Carrier N) : Set where
   constructor is-monoid-homo
   open Monoid M renaming (ε to ε₁ ;  _∙_ to _∙₁_)
   open Monoid N renaming (ε to ε₂ ;  _∙_ to _∙₂_)
   field
    preserves-unit : morph ε₁ ≅ ε₂
    preserves-mult : ∀{x y} → morph (x ∙₁ y) ≅ morph x ∙₂ morph y 

open Monoid-Homomorphism
open Cayley

rep-is-monoid-homo : {M : Monoid} → Is-Monoid-Homo {M} {Cayley M} (rep M)
rep-is-monoid-homo {M} = record {
                         preserves-unit = ext (λ y → lid)
                       ; preserves-mult = ext (λ r → assoc) }
                  where open Monoid M

--------------------------------------------------
{- Ejercicio: Probar que length es un homorfismo de monoides -}

length : {A : Set} → List A → ℕ
length [] = 0
length (x ∷ xs) = 1 + length xs

length-preserves-mult : {A : Set} -> (x y : List A) →
      length (x ++ y) ≅ (length x) + (length y)
length-preserves-mult [] y = refl
length-preserves-mult (x ∷ xs) y = cong suc (length-preserves-mult xs y)

length-is-monoid-homo : {A : Set} -> Is-Monoid-Homo {ListMonoid A} {NatMonoid} length
length-is-monoid-homo {A} = record {
                        preserves-unit = refl
                      ; preserves-mult = \{x}{y} -> length-preserves-mult x y }

--------------------------------------------------

module Foldr (M : Monoid) where

 open Monoid M

 {- Ejercicio : Definir foldr y probar que (foldr _∙_ ε) es un homorfismo de monoides -}

 foldr : {A B : Set} → (A → B → B) → B → List A → B
 foldr _⊗_ e [] = e
 foldr _⊗_ e (x ∷ xs) = x ⊗ (foldr _⊗_ e xs)

 foldr-pmult : (x y : List Carrier) →
      foldr _∙_ ε (x ++ y) ≅ (foldr _∙_ ε x) ∙ (foldr _∙_ ε y)
 foldr-pmult [] y = sym lid
 foldr-pmult (x ∷ xs) y = proof
                          x ∙ foldr _∙_ ε (xs ++ y)
                          ≅⟨ cong₂ _∙_ refl (foldr-pmult xs y) ⟩
                          x ∙ (foldr _∙_ ε xs ∙ foldr _∙_ ε y)
                          ≅⟨ sym assoc ⟩
                          (x ∙ foldr _∙_ ε xs) ∙ foldr _∙_ ε y
                          ∎

 foldr-is-monoid-homo : {A : Set} -> Is-Monoid-Homo {ListMonoid Carrier}{M} (foldr _∙_ ε)
 foldr-is-monoid-homo = record { preserves-unit = refl
                               ; preserves-mult = \{x y} -> foldr-pmult x y }

--------------------------------------------------

{- Isomorfismos entre conjuntos -}

record Iso (A : Set)(B : Set) : Set where
  field fun : A → B
        inv : B → A
        law1 : ∀ b → fun (inv b) ≅ b
        law2 : ∀ a → inv (fun a) ≅ a

open Iso

-----------------------------

{- Ejercicio : introducir un tipo de datos ⊤ con un único habitante y
probar que  ℕ es isomorfo a List ⊤ -}
module list⊤ where
  data ⊤ : Set where
    Top : ⊤

  ℕtolist⊤ : ℕ -> List ⊤
  ℕtolist⊤ zero = []
  ℕtolist⊤ (suc x) = Top ∷ ℕtolist⊤ x

  ⊤-only1 : (x : ⊤) -> Top ≅ x
  ⊤-only1 Top = refl

  ⊤-law1 :  (b : List ⊤) → ℕtolist⊤ (length b) ≅ b
  ⊤-law1 [] = refl
  ⊤-law1 (x ∷ b) = proof
                 Top ∷ ℕtolist⊤ (length b)
                 ≅⟨ cong₂ _∷_ refl (⊤-law1 b) ⟩
                 Top ∷ b
                 ≅⟨ cong₂ _∷_ (⊤-only1 x) refl ⟩
                 x ∷ b
                 ∎

  ⊤-law2 :  (a : ℕ) → length (ℕtolist⊤ a) ≅ a
  ⊤-law2 zero = refl
  ⊤-law2 (suc a) = proof
                 suc (length (ℕtolist⊤ a))
                 ≅⟨ cong suc (⊤-law2 a) ⟩
                 suc a
                 ∎
 


  iso-ℕ-List⊤ : Iso ℕ (List ⊤)
  iso-ℕ-List⊤ = record {
                 fun = ℕtolist⊤
               ; inv = length
               ; law1 = ⊤-law1
               ; law2 = ⊤-law2 }
               
{- Ejercicio: introducir un constructor de tipos Maybe y probar que
Maybe ℕ es isomorfo a ℕ -}
data Maybe (A : Set) : Set where
   Nothing : Maybe A
   Just    : A -> Maybe A

maybe : Maybe ℕ -> ℕ
maybe Nothing = 0
maybe (Just x) = suc x

just : ℕ -> Maybe ℕ
just zero = Nothing
just (suc x) = Just x

maybe-law1 : (b : ℕ) → maybe (just b) ≅ b
maybe-law1 zero = refl
maybe-law1 (suc b) = refl

maybe-law2 : (a : Maybe ℕ) → just (maybe a) ≅ a
maybe-law2 Nothing = refl
maybe-law2 (Just x) = refl

iso-Maybeℕ-ℕ : Iso (Maybe ℕ) ℕ
iso-Maybeℕ-ℕ = record { fun = maybe
                        ; inv = just
                        ; law1 = maybe-law1
                        ; law2 = maybe-law2 }

{- Ejercicio: introducir un constructor de tipos _×_ para productos
cartesianos (o usar el de Data.Product) y probar que (A → B × C) es
isomorfo a (A → B) × (A → C) para todos A, B, y C, habitantes de Set -}
module productIso (A B C : Set) where
    open import Data.Product renaming (proj₁ to proy1; proj₂ to proy2)

    product1 :  {A B C : Set} -> (A → B × C) → (A → B) × (A → C)
    product1 x = (λ y → proy1 (x y)) , (λ y → proy2 (x y))

    product2 : {A B C : Set} -> (A → B) × (A → C) → A → B × C
    product2 (f1 , f2) x = (f1 x) , (f2 x)

    product-law1 : {A B C : Set} -> (b : (A → B) × (A → C)) →
                      product1 (product2 b) ≅ b
    product-law1 (f1 , f2) = refl

    proy-is-cart : {A B : Set} -> (x : A × B) -> (proy1 x , proy2 x) ≅ x
    proy-is-cart (x1 , x2) = refl



    product-law2 : {A B C : Set} -> (a : A → B × C) →
                      (λ x → proy1 (a x) , proy2 (a x)) ≅ a
    product-law2 a = proof
                     (λ x → proy1 (a x) , proy2 (a x))
                     ≅⟨ ext (λ y → proy-is-cart (a y)) ⟩
                     (λ x → a x)
                     ≅⟨ refl ⟩
                     a
                     ∎

    iso-product : {A B C : Set} -> Iso (A -> B × C) ((A → B) × (A → C))
    iso-product = record {
                  fun = product1
                ; inv = product2
                ; law1 = product-law1
                ; law2 = product-law2 }

{- Ejercicio: construir isomorfismos entre Vec A n × Vec B n y
Vec (A × B) n para todos A, B habitantes de Set y n natural -}

module IsoVec (A B : Set) where

 open import Data.Vec
 open CartProduct
 open _×_
 
 vec-fun : {n : ℕ} -> Vec A n × Vec B n → Vec (A × B) n
 vec-fun {zero} ([] , []) = []
 vec-fun {suc n} ((a ∷ as) , (b ∷ bs)) = (a , b) ∷ vec-fun (as , bs)

 vec-inv : {n : ℕ} -> Vec (A × B) n -> Vec A n × Vec B n
 vec-inv {zero} x = [] , []
 vec-inv {suc n} ((x , y) ∷ xs) = (x ∷ proy1 (vec-inv xs)) , (y ∷ proy2 (vec-inv xs))

 proy-is-cart2 : (x : A × B) -> (proy1 x , proy2 x) ≅ x
 proy-is-cart2 (x1 , x2) = refl

 
 vec-law1 : {n : ℕ} -> (b : Vec (A × B) n) → vec-fun (vec-inv b) ≅ b
 vec-law1 {zero} [] = refl
 vec-law1 {suc n} ((a , b) ∷ xs) = 
  proof
    (a , b) ∷ vec-fun (vec-inv xs)
  ≅⟨ cong (_∷_ (a , b)) (vec-law1 xs) ⟩
    (a , b) ∷ xs
  ∎ 

 vec-law2 : {n : ℕ} -> (a : Vec A n × Vec B n) → vec-inv (vec-fun a) ≅ a
 vec-law2 {zero} ([] , []) = refl
 vec-law2 {suc n} ((x ∷ xs) , (y ∷ ys)) = 
        proof
         ((x ∷ proy1 (vec-inv (vec-fun (xs , ys)))) ,
           (y ∷ proy2 (vec-inv (vec-fun (xs , ys)))))
        ≅⟨ cong₂ _,_ (cong (_∷_ x) (cong proy1 (vec-law2 (xs , ys)))) ((cong (_∷_ y) (cong proy2 (vec-law2 (xs , ys))))) ⟩
        ((x ∷ proy1 (xs , ys)) ,
           (y ∷ proy2 (xs , ys)))
        ≅⟨ refl ⟩
        ((x ∷ xs) , (y ∷ ys))
        ∎

 iso-vec : {n : ℕ} -> Iso (Vec A n × Vec B n) (Vec (A × B) n)
 iso-vec = record {
          fun = vec-fun
        ; inv = vec-inv
        ; law1 = vec-law1
        ; law2 = vec-law2 }


