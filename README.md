# Agtor, the god of asynchronous communication.

This is an attempt at a dependently typed actor language. This is highly experimental with a low probability of actually working.

Contrary to pi calculus, we start by putting the constraint that communication should be type safe, disregarding how it happens, ie disregarding the problem
of finding the location of the actor and sending the msg to the specific location. It is assumed that later, one could introduce the restriction of knowing where to send the message.

For example, the same system could potentially be executed in a single machine with multiple cpus or in many machines across the globe. This separation of concerns allows us to treat both systems as the same thing.

It has similar structural congruence properties to pi types, but instead of pi that only has channels,
this language has three types of *particles* :
- Messages : Normal messages that are sent and asyncronously received by actors.
- Actors   : Actors receive msgs and secrets. They respond by creating new msgs, secrets and actors.
- Secrets  : They are special messages that give the actor the ability to interact with other actors who also have the secret.

We use secrets so as to create scope, in other words to limit the outside world that does not have the secret from interacting with actors that require it.

- Reduction needs to be performed globally, and any actor that exists in parallel, could potentially interact with our system. It is for this reason that secrets are so important. They will allow
us to perform local reduction ignoring the outside world.
- Both the environment and the digital computation are treated uniformally as computation. Because we have dependent types , we pressumably do not need linear temporal logic to express liveness properties of the system.
(we might though need to express that all messages are eventually delivered.)
- Nondeterministic computation is expressed with the use of free variables. Multiple free variables could potentially be merged into a single one, if the outcome of the computation depends on the aggregate, for example.
Moreover free variables allows us to have an open system. This means that the type of the system can depend on user input and thus the dynamics of the system can change based on that input.