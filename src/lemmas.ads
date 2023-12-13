with Types; use Types;
with Aux; use Aux;
with Core_Definitions; use Core_Definitions;
with Counting;

package Lemmas with
   Spark_Mode
is


   procedure Admissible_by_Equality (S1 : ArgSet; S2 : ArgSet; F : AF) with
     Ghost,
     Pre => Is_ArgSet(S1,F.Size) and then S1 = S2 and then Admissible(S1,F),
     Post => Admissible(S2,F);

   procedure Defense_by_Equality (S1 : ArgSet; S2 : ArgSet; a: Arg; F : AF) with
     Ghost,
     Pre => Is_ArgSet(S1,F.Size) and then a <= F.Size and then S1 = S2 and then Defends(S1,a,F),
     Post => Defends(S2,a,F);

   procedure Complete_by_Equality (S1 : ArgSet; S2 : ArgSet; F : AF) with
     Ghost,
     Pre => Is_ArgSet(S1,F.Size) and then S1 = S2 and then Complete(S1,F),
     Post => Complete(S2,F);

   procedure Grounded_by_Equality (S1 : ArgSet; S2 : ArgSet; F : AF) with
     Ghost,
     Pre => Is_ArgSet(S1,F.Size) and then S1 = S2 and then Grounded(S1,F),
     Post => Grounded(S2,F);

   -- Lemma: If R defends a and every complete extension contains R, then every complete extension contains a.
   procedure Every_Complete_Extension_Contains (a : Arg; R : ArgSet; F : AF) with
     Ghost,
     Pre => Is_ArgSet(R,F.Size) and then
            a <= F.Size and then
            Defends(R,a,F) and then
            (for all I in Arbitrary_ArgSets(F.Size)'Range =>
               (if Complete(Arbitrary_ArgSets(F.Size)(I),F) then Subset(R,Arbitrary_ArgSets(F.Size)(I)))),
     Post => (for all I in Arbitrary_ArgSets(F.Size)'Range => (if Complete(Arbitrary_ArgSets(F.Size)(I),F) then Arbitrary_ArgSets(F.Size)(I)(a)));

   function Search_Acceptable_Arg (S : ArgSet; F : AF) return SearchResult with
     Pre => Is_ArgSet(S,F.Size),
     Post => (if not Search_Acceptable_Arg'Result.Exists then
                (for all a in 1 .. F.Size => (if not S(a) then not Defends(S,a,F)))) and then
             (if Search_Acceptable_Arg'Result.Exists then
                (Search_Acceptable_Arg'Result.Arg <= F.Size and
                not S(Search_Acceptable_Arg'Result.Arg) and
                Defends(S,Search_Acceptable_Arg'Result.Arg,F)));

   procedure Extend_Admissible_List (L : in out ArgList; a : in Arg; F : in AF) with
     Pre => Is_ArgList_For(L,F.Size) and then
            Is_ArgSet(ArgSet_From_ArgList(L,F.Size),F.Size) and then
            a <= F.Size and then
            not ArgSet_From_ArgList(L,F.Size)(a) and then
            Admissible(ArgSet_From_ArgList(L,F.Size),F) and then
            Defends(ArgSet_From_ArgList(L,F.Size),a,F),
     Post => Is_ArgList_For(L,F.Size) and then
             ArgSet_From_ArgList(L,F.Size)(a) and then
             L'Old.Size < L.Size and then
             (for all b in 1 .. F.Size => (if ArgSet_From_ArgList(L,F.Size)(b) and b /= a then ArgSet_From_ArgList(L'Old,F.Size)(b))) and then
             Admissible(ArgSet_From_ArgList(L,F.Size),F);

   procedure Extend_Admissible (S1 : in ArgSet; S2 : in ArgSet; a : in Arg; F : in AF) with
     Ghost,
     Pre => (Is_ArgSet(S1,F.Size) and then Is_ArgSet(S2,F.Size) and then a <= F.Size and then not S1(a) and then S2(a) and then Subset(S1,S2) and then (for all b in 1 .. F.Size => (if S2(b) and b /= a then S1(b))) and then Admissible(S1,F) and then Defends(S1,a,F)),
     Post => (Admissible(S2,F));

 end Lemmas;
