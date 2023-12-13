with Types; use Types;

package Aux with
   Spark_Mode
is


   function Subset (S1 : ArgSet; S2 : ArgSet) return Boolean is
     (for all a in 1 .. MaxNumberOfArgs => (if S1(a) then S2(a)));

   function Is_ArgSet (S : ArgSet; N : AFSize) return Boolean is
     (for all a in N+1 .. MaxNumberOfArgs => not S(a));

   function Is_ArgList_For (L : ArgList; N : AFSize) return Boolean is
     (L.Size <= N and (for all I in 1 .. L.Size => L.List(I) <= N));

   function ArgSet_From_ArgList (L : ArgList; N : AFSize) return ArgSet with
     Pre => Is_ArgList_For(L,N),
     Post => Is_ArgSet(ArgSet_From_ArgList'Result,N) and then
             (for all I in 1 .. N => not (ArgSet_From_ArgList'Result(I) xor (for some J in 1 .. L.Size => L.List(J) = I)));


   -- The following two functions are for quantifying over ArgSets and reasoning qith such quantifications:
   function Arbitrary_ArgSets (N : AFSize) return ArgSetArray with
     Ghost,
     Post => Arbitrary_ArgSets'Result'First <= Arbitrary_ArgSets'Result'Last and then
             (for all I in Arbitrary_ArgSets'Result'Range => Is_ArgSet(Arbitrary_ArgSets'Result(I),N));

   function Exists_ArgSet_Intro (N : AFSize; S : ArgSet) return Positive with
     Ghost,
     Pre => Is_ArgSet(S,N),
     Post => Exists_ArgSet_Intro'Result in Arbitrary_ArgSets(N)'Range and then
             S = Arbitrary_ArgSets(N)(Exists_ArgSet_Intro'Result);


end Aux;
