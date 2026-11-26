#import "common.typ" : *

= Theory and practice

#note[TODO :
        - provide references for Enactivism. 
              ]

#note[
subjectivity / variability and formal system incompleteness
thus, we need to have these properties:
- liveness: Theories should change as we go, in the context of action, they should be ephemeral, while we continue to act.
- adaptiveness: theories should be able to allow to react to change without requiring a change in theory.
- Open system: No ontology can capture all possible theories, thus we need to allow for full flxibility to construct any theory.
]
What does it mean to construct a theory of the world? Living beings construct theories that will help them cope with the world, that helps them survive. In that regard, the theory is subject dependent, what is important for one living organism is different than another. What is more, changes in the environment or the organism itself can have unpredictable consequences. It is not possible to predict beforehand of all the possible states that the world will be, because the world is complex. Any formal description of the world will not be able to describe all the properties of the world.

#note[Enactivism / temporality / contextuality / interactivity]
It is for this reason that one cannot seperate the theory from the practice, or the theory from the organism who made the theory. Theories are temporal and can only be understood / created inside a specific context. Theories are interactive, meaning that they continually change as we interact with the environment in context. This philosophical perspective is called Enactivism.

#note[Examples]
The world of a snail is different from the world of a human. A climber 
views differently the mountain rocks than a hiker.

Believing that AI will become superintelligent in approximately 10 years and thus solve all social problems, including the climate crisis has convinced you to expand the construction of new data centers , the consumption of even more energy and thus the acceleration of climate change. A world of extreme and unlivable weather conditions will require new solutions that were not necessary before. Your previous theory of AI superintelligence changed the world.

From the above examples, I want to point that an update of a theory does not mean that we construct of a new theory that is more precise, in the same stable world. This is possible in simple systems like physics, but not in complex systems. In our case, the world and the theory change at the same time.

#note[Organisms and Autonomy]
Matteo Mossio et al. #cite(label("montevil:hal-01379202")) considers this a property of organisms. He points that Biology's object of research, the organism, is #emph([specific]); There are no generic rules that can dictate the behavior of an organism. Because of that and because of the orgamism's effort to reconstruct itself, organisms are autonomous, meaning that they have an internal "state" that allows them to make unpredictable decisions.

#note[Autonomous systems as freedom / agency preserving systems]
We are interested in theories that are specific, because we are interested in theories of systems in which the observer is part of the system. We want our social systems to be autonomous, to adapt in unpredictable ways. Systems that are not autonomous only lead to the control of humans. Historically, second order cybernetics were interested in modeling systems that would restrict some variables to specific boundaries, they were thus methods of control and not of enabling human creativity and freedom. #cite(label("10.5281/ZENODO.21416181"))

An informal description of a human being interacting with the world is defined at @inf-m.

A formal model is a mathematical model that describes part of our informal theory , that can enable us to infer interesting properties of our system. These properties can then be used to identify possible ways of acting in the environment.

#figure(
 diagram(
   spacing: 40mm,
 {
   node((0,-1) , [Formal Model] , name: "mdl")
   node((0.02 ,-0.5) , [Theory] , name: "thr")
   edge("<-" , name: "thr-l")
   node((0,0) , [person] , name: "usr")
   edge("->" , <mdl> , name: "mdl-l" , bend: +50deg)
   edge(<thr> , "->" , <mdl-l>)
   edge("->" , loop: 270deg , size: 30pt , name: "usr-l")
   node((1,0) , [environment] , name: "env")
   edge("->" , loop: 180deg , size: 30pt , name: "env-l")
   edge(<usr> , "->" , <env-l> , label:((body: "actions" , side: bottom)), name: "act")
   edge(<env> , <usr-l> , "->" , label: ((body: "information", side: bottom)) , bend: +50deg )
   edge(<env> , <usr-l> , "->" , label: ((body: "perceived information", side: bottom , sep: 14pt)) , bend: +80deg , name: "pinf")
   edge(<thr> , <pinf> , "-->" , label: ((body: "interprets", side: bottom , angle: auto)) , bend: -80deg)
   edge(<mdl> , <pinf> , "-->" , label: ((body: "decodes", side: bottom , angle: auto)) , bend: -90deg )
   edge(<thr> , <act> , "-->" , label: ((body: "guides", side: bottom , angle: auto)))
   edge(<mdl> , <act> , "-->" , label: ((body: "encodes options", side: top , angle: auto)))
 }),
 caption: [An informal model]
) <inf-m>




#cite(label("10.3389/fphys.2020.00069"))

