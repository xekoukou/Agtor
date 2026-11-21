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

There are two possible alternatives to this. The first is the composition of software in such a way that applications are small and tractable. In this case, software should be malleable, demanding the least amount of technical skill. This raises the question: Who is responsible for providing this malleable substrate? Developers, once again. Thus, this alternative is disingenious in hiding the fact that there are developers that povide the language / substrate that users interact with. Nonetheless, here, there is substantial effort to expand the number of possible actions available so as not to control the user. But other questions still remain. Who supports economically the developers if they are supposed to be absent from public view? Who can guarantee that the developers will continue to develop substrates that respect and enable the users? As we can see, the problems of the previous model of development still persist in this case.

#figure(
 diagram(
   spacing: 40mm,
 {
   node((-1,-1) , [Specification] , name: "mdl")
   node((0,-1) , [Application] , name: "app")
   node((-1,-0.5) , [Theory] , name: "scn-th")
   node((-1,0) , [scientists] , name: "scn")

   node((0 ,-0.5) , [Theory] , name: "thr")
   node((0,0) , [community] , name: "grp")
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

The second option is to have a group of scientists and developers work together with the community that will use the software. As we have described before, theories form in context during the interaction with the environment. Theories change, they are ephemeral. Theories are specific. Thus, since the application acts as an interface with the environment, the app needs to be custom made and constantly adapt to the needs of the community. How can a group of experts help the community in that regard?

- The community describes its needs and interests to them. The experts should be embedded in the community or at least have physical interaction with it so as to perceive its unwritten rules and customs.

- The experts need to construct a theory based on those needs and at the same time explain the theory to the community so as to form its own understanding. It is here that we need to build tools for the communal guided exploration of the space of possibilities, tools like #link("https://dynamicland.org/")[dynamicland].
- As soon as the theory has been finalized, the experts define a specification fo the possible interactions with the environment. The specification is based on the needs of the group but also on the current environmental conditions, including the state of the rest of the society.

- The *specification* describes the constrains imposed on the interface of the application. At the same time, it expresses the possible degrees of freedom when developing the application. It is here that the community can decide on the way the app is developed so as to align better with its needs. This is one way that the community is *autonomous* from its environment.

It is important to understand this process in terms of the *adaptability* of the application, when the community and the environment constantly coevolve.
There are two dinstinct ways that the application changes its dynamics.

- The application can have an *internal logic* to adapt to changes of the world. In other words, the experts and the community have anticipated the new state and have developed the application to change its behavior.
- But *nature* and *organisms* are *complex systems*. There is no theory that can anticipate all the possible changes of the organism and its environment #cite(label("montevil:hal-01379202")). It is for this reaon that the interaction of the community with the experts is persistent, because the theory and the app will need to change eventually. This is not a problem of optimization. It has to do with the fact that as time passes, new ontologie are formed which could not have been predicted beforehand.

By understanding that organisms are complex and thus autonomous, the application does not only constrain the space of possibilities of the community. The community creates its own *space of possibilities* by adapting the application in unpredictable ways. As Donna Haraway#cite(label("Haraway2016")) would put it, the community engages in an act of worlding, the embodied construction of new ontologies of the world. The community plays the important role of identifying what is relevant and adapting its point of view. #cite(label("10.3389/fpsyg.2024.1362658"))


