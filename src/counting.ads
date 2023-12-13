with Types; use Types;
with Aux; use Aux;

package Counting with
   Spark_Mode
is


   procedure ArgList_Not_Full (L : ArgList; N : AFSize) with
     Ghost,
     Pre => Is_ArgList_For(L,N) and then (not (for all b in 1 .. N => ArgSet_From_ArgList(L,N)(b))),
     Post => L.Size < N;

   procedure Quantified_Substitution_Of_Equals (A : NatArray; N : AFSize; L : ArgList) with
     Ghost,
     Pre => A'First <=1 and then A'Last >= N and then
            (for all J in 1 .. N => A(J) = J) and then
            Is_ArgList_For(L,N) and then
            not (for all J in 1 .. N => ArgSet_From_ArgList(L,N)(J)),
     Post => not (for all J in 1 .. N => ArgSet_From_ArgList(L,N)(A(J)));

   procedure Substitution_Of_Equals (A : NatArray; J : Natural; N : AFSize; L : ArgList) with
     Ghost,
     Pre => J in A'Range and then A(J) = J and then Is_ArgList_For(L,N) and then ArgSet_From_ArgList(L,N)(A(J)),
     Post => ArgSet_From_ArgList(L,N)(J);

   function Array_Contains (A : NatArray; N : Natural; K : Natural) return Boolean is
     (not (for all I in 1 .. N => A(I) /= K)) with
       Pre => A'First <= 1 and A'Last >= N;

   procedure Remove_Elt_From_Array (b : Arg; A : in out NatArray; N : Natural; K : Natural) with
     -- Intuitively, A is an array of numbers between 1 and N of length K, and we remove the element b from it.
     Ghost,
     Pre => N <= MaxNumberOfArgs and then
            K <= N and then
            (for all J in 1 .. K => A(J) in 1 .. N) and then
            (for some I in 1 .. K => A(I) = b),
     Post => (for all J in 1 .. K-1 => A(J) in 1 .. N) and then
             (for all J in 1 .. N => (if J /= b and (for some I in 1 .. K => A'Old(I) = J) then
                (for some I in 1 .. K-1 => A(I) = J)));


end Counting;
