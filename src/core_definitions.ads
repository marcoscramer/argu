with Types; use Types;
with Aux; use Aux;


package Core_Definitions with
   Spark_Mode
is


   function Attacks (a : Positive; b : Positive; F : AF) return Boolean is
     (F.AdjacencyMatrix(a,b)) with
       Pre => a <= F.Size and then b <= F.Size;

   function Conflict_Free (S : ArgSet; F: AF) return Boolean is
     (for all a in 1 .. F.Size => (for all b in 1 .. F.Size =>
          (if S(a) and S(b) then not Attacks(a,b,F)))) with
       Pre => (Is_ArgSet(S,F.Size));

   function Defends (S : ArgSet; a : Positive; F : AF) return Boolean is
     (for all b in 1 .. F.Size => (if Attacks(b,a,F) then
         (for some c in 1 .. F.Size => (S(c) and Attacks(c,b,F))))) with
       Pre => (Is_ArgSet(S,F.Size) and then a <= F.Size);

   function Admissible (S : ArgSet; F : AF) return Boolean is
     (Conflict_Free(S,F) and then (for all a in 1 .. F.Size => (if S(a) then Defends(S,a,F)))) with
       Pre => (Is_ArgSet(S,F.Size));

   function Complete (S : ArgSet; F : AF) return Boolean is
     (Admissible(S,F) and then (for all a in 1 .. F.Size => (if Defends(S,a,F) then S(a)))) with
       Pre => (Is_ArgSet(S,F.Size));

   function Grounded (S : ArgSet; F : AF) return Boolean is
     (Complete(S,F) and then
          (for all I in Arbitrary_ArgSets(F.Size)'Range =>
             (if Subset(Arbitrary_ArgSets(F.Size)(I),S) and Complete(Arbitrary_ArgSets(F.Size)(I),F) then
                 S = (Arbitrary_ArgSets(F.Size)(I))))) with
       Ghost,
       Pre => (Is_ArgSet(S,F.Size));

   function Preferred (S : ArgSet; F : AF) return Boolean is
     (Complete(S,F) and then
          (for all I in Arbitrary_ArgSets(F.Size)'Range =>
             (if Subset(S,Arbitrary_ArgSets(F.Size)(I)) and Complete(Arbitrary_ArgSets(F.Size)(I),F) then
                 S = (Arbitrary_ArgSets(F.Size)(I))))) with
       Ghost,
       Pre => (Is_ArgSet(S,F.Size));


end Core_Definitions;
