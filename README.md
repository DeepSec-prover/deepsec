**_IMPORTANT NOTE:_** *All installation and usage information below can be found in the official [DeepSec website](https://deepsec-prover.github.io) with more details, a tutorial for the tool, and references to academic publications.*

# DeepSec: Deciding Equivalence Properties in Security Protocols

Automated verification has become an essential part in the security evaluation of cryptographic protocols. Recently, there has been a considerable effort to lift the theory and tool support that existed for reachability properties to the more complex case of equivalence properties. **DeepSec** allows you to decide trace equivalence and session equivalence for a large variety of cryptographic primitives---those that can be represented by a subterm convergent destructor rewrite system.

## How to install DeepSec?

**DeepSec** has been successfully tested on Linux and MacOSX (Windows is currently not supported). **DeepSec** requires **OCaml > 4.05**.  It is highly recommended to install **OCaml** through `opam` instead of a native package manager, such as `apt-get` (the latest version on `apt-get may` not be the latest release of OCaml). `opam` itself may however be safely installed using your favorite package manager (see instructions for installing `opam`).

### Upgrading Ocaml using OPAM 1.x.x

1. Run `opam switch list` (The version 4.05.0 should be displayed in the list. Otherwise run first `opam update`)
2. Run `opam switch 4.05.0` (or a more recent version)
3. Follow the instructions (at the end do not forget to set the environment by running ``eval `opam config env` ``)

### Upgrading Ocaml using OPAM 2.x.x

1. Run `opam switch list-available` (The version `ocaml-base-compiler 4.05.0` should be displayed in the list. Otherwise run first `opam update`)
2. Run `opam switch create 4.05.0` (or a more recent version)
3. Follow the instructions

### Installation of DeepSec from source

**Deepsec** requires the package **ocamlbuild** to compile which itself requires **ocamlfind**. It is important that both ocamlbuild and ocamlfind are compiled with the same version of Ocaml. Running `opam install ocamlbuild` may not install ocamlfind if an instance of ocamlfind was installed on a different installation of Ocaml (which sometimes happen on MacOsX). It's safer to run `opam install ocamlfind` before.

1. Run `opam install ocamlfind` (Optional if already installed)
2. Run `opam install ocamlbuild` (Optional if already installed)
3. Run `git clone https://github.com/DeepSec-prover/deepsec.git` (with a HTTPS connexion) or `git clone git@github.com:DeepSec-prover/deepsec.git` (with a SSH connexion)
4. Inside the directory `deepsec`, run `make`
5. The executable program `deepsec` has been built.

Note that two executable programs are compile at the same time as `deepsec`: `deepsec_worker` and `deepsec_api`. The former is used by **DeepSec** to distribute the computation through multi-core architectures and clusters of computers. The latter is used to communicate with the UI (available at https://github.com/DeepSec-prover/deepsec_ui). Both should not be used manually nor should they be moved from the `deepsec` folder.

## How to use DeepSec?

### Input grammar

To use **DeepSec**, you first need to specify your security protocol inside a file. The input grammar of **DeepSec** is very similar to the untyped input grammar of **[ProVerif](http://prosecco.gforge.inria.fr/personal/bblanche/proverif/)**. Examples of input files can be found in the **DeepSec** repository.

Free and privates names can be defined using the keyword `free`.

```
free ca, cb.
free c.

free ska, skb, skc [private].
```

Construction function symbols are defined with the keyword `fun`. Note that the arity of the function symbol shall be provided.

```
fun aenc/2.
fun pk/1.
```

Constants can be declared either using the keyword fun or the keyword const.

```
const ok.
fun bad/0.
```

Destructor function symbols are defined by the rewrite rules that describe their cryptographic behavior, using the keyword `reduc`.

```
reduc adec(aenc(x,pk(y)),y) = x.
```

Note that if a destructor function require several rewrite rules, they should be defined inside the same reduc.

```
reduc
  exists_double(x,x,y) -> ok;
  exists_double(x,y,x) -> ok;
  exists_double(y,x,x) -> ok.
```

Recall that **DeepSec** requires that the set of rewrite rules are destructor subterm convergents. In this alpha version of the tool, **DeepSec** does not check if the rewrite system satisfy this condition and the verification is left to the user.

Processes can be declared using the keyword `let`. Note that processes can have arguments.

```
let processA(ca,ska,pkb) =
  new na;                            // Name restriction
  out(ca,aenc((na,pk(ska)),pkb));    // Output of the message aenc((na,pk(ska)),pkb)
                                     // on the channel ca
  in(ca,x).                          // Input of x on the channel ca
```

Conditionals can be expressed as `if u = v then P else Q` or as `let pat = u in P else Q`.

```
let processB(cb,skb,pka) =
  in(cb,yb);
  new nb;
  let (yna,=pka) = adec(yb,skb) in
    out(cb,aenc((yna,nb,pk(skb)),pka))
  else out(cb,aenc(nb,pk(skb))).
```

The process `let pat = u in P else Q` tries  to first reduce all destructor symbol in `u` and second to instantiate the pattern `pat` such that it becomes equal to `u`. If successful, `P` is executed otherwise `Q` is executed. In the previous exemple, the process `out(cb,aenc((yna,nb,pk(skb)),pka))` is executed if there exists an instantiation of the variable `yna` such that `yb = aenc((yna,pka),pk(skb))`. Note that in the pattern `(yna,=pka)`, `yna` is a fresh variable whereas `=pka` represents a term equality.

Note that processes can call other previously declared processes.

```
let ProcessAB =
  out(c,pk(ska));
  out(c,pk(skb));
  out(c,pk(skc));
  (
    processA(ca,ska,pk(skb)) | processB(cb,skb,pk(ska))
  ).

let ProcessCB =
  out(c,pk(ska));
  out(c,pk(skb));
  out(c,pk(skc));
  (
    processA(ca,skc,pk(skb)) | processB(cb,skb,pk(skc))
  ).
```

Finally, trace equivalence queries are declared using the keyword `query`.

```
query trace_equiv(ProcessAB,ProcessCB).
```

Currently there are three possible types of query: **trace equivalence** (`query trace_equiv(A,B).`), **session equivalence** (`query session_equiv(A,B).`) and **session inclusion** (`query session_incl(A,B).`).  Trace equivalence is the standard equivalence. Session equivalence is stronger than trace equivalence and requires some light syntactic restriction (ex: syntactic channel). However, the verification of session equivalence is much faster generally (except in the case whether the processes are determinate).

An input file can contain several queries.

### Executing the input file

To run the input file, the simplest way is to run `deepsec <name of the file>`. Once the computation is completed, **DeepSec** displays the result.

For example, running `deepsec Examples/trace_equivalence/Private_authentication/PrivateAuthentication-1session.dps` would output the following.

```
DeepSec - DEciding Equivalence Properties for SECurity protocols
    Version: 2.0.0
    Git hash: 33e38cfd1c33f47bf3e2b678559bd4286be373c0
    Git branch: master

Loading file Examples/trace_equivalence/Private_authentication/PrivateAuthentication-1session.dps...

Starting verification...

Starting verification of PrivateAuthentication-1session.dps...
Result query 1: The two processes are trace equivalent. Verified in < 1s                                          
Verification complete.
```

To see more information, it is highly recommended to use **[DeepSec UI](https://github.com/DeepSec-prover/deepsec_ui)**. With the user interface, you can see the input processes, the summary of the declared name, function symbols and rewrite rules for each query. Moreover when an attack is found on one process of the query, **DeepSec UI** can show you step-by-step the attack trace on this process and it is possible to also simulate the other process to better understand why this trace is an attack trace. Similarly, when the two processes are equivalent, an **equivalence simulator** is available in which one can select a trace of one of the processes and request from the UI an equivalent trace on the other process.

Note that **DeepSec** can take several files as input. Ex: `deepsec file1 file2 file3`

### Distributed computation

By default, **DeepSec** checks how many physical core your machine have and distribute the computation on these core by creating the same amount of workers. To activate the distributed computation with a different number of workers, `deepsec` should be run with the option `-l n` (or `--local_workers n`) where `n` is the number of desired local workers. It is also possible to distribute computation through several computers. To do so, deepsec requires an ssh connexion between the localhost and the distant machine. The computation on distant machine must be configured with the option `-w <host> <path> <n>` (or `--distant_workers <host> <path> <n>`). The parameter `<host>` is the ssh login and address (e.g my_login@my_host). The parameter `<path>` should indicate the path on the distant machine the deepsec directory. Finally the parameter `<n>` represents the number of cores that should be dedicated by this distant machine to the computation of the input file. As connections to distant machines are performed through ssh we recommend to configure a passwordless authentication, e.g., using ssh keys.

Note that that the option `-distant_workers` should be used for each distant machine.

```
deepsec -w login1@host1 tools/deepsec 15 -w login2@host2 deepsec 35 my_file.dps
```

In this command line, the first machine should be accessible with `ssh login1@host1` and the **DeepSec** directory should be located at `~/tools/deepsec` on this machine. Similarly, the second machine should be accessible with `ssh login2@host1` and the **DeepSec** directory should be located at `~/deepsec`. If the connexions to both machines are successful, **DeepSec** will distribute the computation of the file `my_file.dps` between 20 local cores, 15 cores on the first machine and 35 on the second machine.

**_IMPORTANT_**: The localhost and distant machines should have exactly the same version of **DeepSec** (The Git hash is displayed when running `deepsec` without parameters or with the option `--help`) compiled with the same version of **OCaml**.
