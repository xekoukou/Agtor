#import "common.typ" : *

= Application development and user interaction 

How can our theory of the world guide the development of digital applications? It would be informative to first look at the current way that applications develop.

#figure(
 diagram(
   spacing: 50mm,
 {
   node((0,0) , [user] , name: "usr")
   edge("->" , loop: 270deg , size: 30pt , name: "usr-l")
   node((1,0) , [environment] , name: "env")
   edge("->" , loop: 180deg , size: 30pt , name: "env-l")
   edge(<usr> , "->" , <env-l> , [digital actions], bend: +20deg , name: "dact")
   edge(<usr> , "->" , <env-l> , [physical actions], bend: -10deg , name: "phact")
   node((0, -0.5) , [developers] , name: "dev")
   edge("->")
   node((0.40, -0.5) , [Application] , name: "app")
   edge(<env> , <usr-l> , "->" , label: ((body: "physical interaction", side: top)) , bend: +50deg )
   edge(<env> , <usr-l> , "->" , [digital interaction], bend: +70deg , name: "diact")
   edge(<app> , "-->" , <dact> , bend: -10deg)
   edge(<app> , "-->" , <diact> , bend: +10deg)
 }),
 caption: [Standard method of development.]
)

In the standard model of development, both free software and closed source, the developers are different from the users. The application provides the type of actions that the user can perform, and interprets and filters the information that the environment gives back to the user.

There are two possible alternatives to this. The one is the composition of software in such a way that applications are small and tractable. In this case, software should be malleable, demanding the least amount of technical skill. This raises the question: Who is responsible for providing this malleable substrate? Developers, once again. Thus, this alternative is disingenious in hiding the fact that there are developers that povide the language / substrate that users interact with. Nonetheless, here, there is substantial effort to expand the number of possible actions available so as not to control the user. But other questions still remain. Who supports economically the developers if they are supposed to be absent from public view? Who can guarantee that the developers will continue to develop substrates that respect and enable the users? As we can see, the problems of the previous model of development still persist in this case.

#figure(
 diagram(
   spacing: 40mm,
 {
   node((-1,-1) , [Specification] , name: "mdl")
   node((0,-1) , [Application] , name: "app")
   node((-1,-0.5) , [Theory] , name: "scn-th")
   node((-1,0) , [scientists] , name: "scn")

   node((0 ,-0.5) , [Theory] , name: "thr")
   node((0,0) , [group] , name: "grp")
   node((1.7,0) , [environment] , name: "env")

   edge(<scn> , "<-" , loop: 360deg , size: 25pt , name: "scn-l")
   edge(<grp> , "<-" , loop: 360deg , size: 25pt , name: "grp-l")
   edge(<env>, "->" , loop: 180deg , size: 25pt , name: "env-l")

   edge(<scn> , "->" , <scn-th>)
   edge(<scn> , "->" , <mdl> , name: "mdl-l" , bend: +50deg)
   edge(<scn-th> , "->" , <mdl-l>)

   edge(<grp> , "->" , <thr> , name: "thr-l")
   edge(<grp> , "->" , <scn-l> , label:((body: "describes interests" , side: bottom)))
   edge(<grp-l> , "<=>" , <env-l> , label:((body: "digital interactions" , side: bottom)), bend: +20deg , name: "dact")
   edge(<grp-l> , "<=>" , <env-l> , label:((body: "physical interactions" , side: bottom)), bend: -30deg, name: "pact")


   edge(<scn> , "->" , <thr-l> , label:((body: "explain theory" , side: top , angle: auto)) , name: "exp")
   edge(<exp> , "<-" , <scn-th>)

   edge(<scn> , "->" , <app>, name: "dev")
   edge(<mdl> , "-->" , <dev> , label: ((body: "bounds" , side:top , angle:auto)))
   edge(<grp> , "-->" , <dev>,  label: ((body: "decides" , side:top , angle:auto)) , bend: -10deg)

   edge(<app> , "...>" , <dact> , label: ((body: "encodes" , angle:auto , side: bottom) , (body: "restricts" , angle:auto , side: top)))
   edge(<thr> , "-->" , <dact> , label: ((body: "interprets" , angle:auto , side: bottom)))
 }),
 caption: [A method of development where the group is directly connected with a group of scientists.]
) <inf-2>



#note[How can we democratically produce new theories.
How would one describe a system that uses an application?]

#cite(label("10.3389/fphys.2020.00069"))

