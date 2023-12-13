------------------------------------------------------------------------------
--                                                                          --
-- A verified tool for finding and checking the grounded extention of an    --
-- argumentation framework. The existence and uniqueness of the grounded    --
-- extension as well as the existence of preferred extensions have been     --
-- verified based on a trick for imlpementing higher-order quantification   --
-- in SPARK.                                                                --
--                                                                          --
------------------------------------------------------------------------------
--                                                                          --
-- GNU General Public License v2.0, Marcos Cramer, 2023                     --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Text_IO;
--with Ada.Command_Line; use Ada.Command_Line;

with Input_Output; use Input_Output;
with Types; use Types;

procedure Main
with
  SPARK_Mode => Off
is
   CheckResult : Boolean;
   EmptySet : InputArgList (1 .. 0);

begin

   -- Find the grounded extension of a given argumentation framework:

   Print_ArgList(Grounded_Input_Output(

   -- Put input AF here.
   -- Notation: Array of edges of the AF. Each edge is a pair of integers
   -- between 1 and 1000.
   -- The set of nodes is automatically derived to be the set of positive
   -- integers less that or equal to the largest integer mentioned in an edge.
   -- Example:
   -- ((2,3),(4,4),(4,2),(2,5))

   ((1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,6),(9,9),(9,1),(10,2))

   ));


   -- Check whether a given set of arguments is the grounded extension of
   -- a given argumentation framework:

   CheckResult := Check_Grounded_Input_Output(

   -- Put input AF here (see clarifications on the notation above):

   ((1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,6),(9,9),(9,1),(10,2))

   ,
   -- Put the set of arguments here as an array of integers between 1 and 1000:
   -- Notation: Array of numbers.
   -- For the empty set, write "EmptySet".
   -- For the singleton {x}, write "Singleton(x)".
   -- For sets with more elements, use curly brackets and commas, e.g. (2,3,5)

   (5,7,10,3,3,3,3,3)

   );

   if CheckResult then
      Ada.Text_IO.Put("Yes");
   else
      Ada.Text_IO.Put("No");
   end if;

end Main;
