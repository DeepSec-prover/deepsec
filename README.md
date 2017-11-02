# DeepSec: Deciding Equivalence Properties in Security Protocols

Automated verification has become an essential part in the security evaluation of cryptographic protocols. Recently, there has been a considerable effort to lift the theory and tool support that existed for reachability properties to the more complex case of equivalence properties. In this paper we contribute both to the theory and practice of this verification problem.  We establish new complexity results for static equivalence, trace equivalence and labelled bisimilarity and propose a new decision procedure for these equivalences in the case of a bounded number of sessions. Our procedure provides the first tool to decide trace equivalence and labelled bisimilarity exactly for a large variety of cryptographic primitives---those that can be represented by a subterm convergent destructor rewrite system. We implemented the procedure in a new tool, **DeepSec**. We perform an extensive experimental verification showing that our tool is significantly more efficient than many other similar tools, while at the same time raises the scope of the protocols that can be analyzed.

## How to install DeepSec?

**DeepSec** has been successfully tested on Linux and MacOSX (Windows is currently not supported). **DeepSec** requires **OCaml > 4.03**.  It is highly recommended to install **OCaml** through `opam` instead of a native package manager, such as `apt-get` (the latest version on `apt-get may` not be the latest release of OCaml). `opam` itself may however be safely installed using your favorite package manager (see instructions for installing `opam`).

### Upgrading Ocaml using OPAM

1. Run `opam switch list` (The version 4.05.0 should be displayed in the list. Otherwise run first `opam update`)
2. Run `opam switch 4.05.0` (latest official release)
3. Follow the instructions (at the end do not forget to set the environment by running ``eval `opam config env` ``)

### Installation of DeepSec

1. Run `git clone https://github.com/DeepSec-prover/deepsec.git` (with a HTTPS connexion) or `git clone git@github.com:DeepSec-prover/deepsec.git` (with a SSH connexion)
2. Inside the directory `deepsec`, run `make`
3. The executable program `deepsec` has been built.
4. Add the `deepsec` executable to your path, e.g. if your shell is bash, add the line `export DEEPSEC_DIR=<path to the deepsec folder>/deepsec` to the .bash_profile file

The fourth step is not mandatory but highly recommended. If the variable `DEEPSEC_DIR` is not defined, `deepsec` can only be used with the option `-deepsec_dir <path to the deepsec folder>/deepsec`.

Note that two executable programs are compile at the same time as `deepsec`: `worker_deepsec` and `manager_deepsec`. These executables are used by DeepSec to distribute the computation through multi-core architectures and clusters of computers. They should note be used manually nor should they be moved from the `deepsec` folder.

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

An input file can contain several queries.
Executing the input file

To run the input file, the simplest way is to run `deepsec <name of the file>`. Once the computation is completed, **DeepSec** generates a HTML page, `index.html`, in the current directory containing a summary of the queries, the computation time and the results of each query. Additional files are generated for each query displaying the input processes, the summary of the declared name, function symbols and rewrite rules. Moreover, in case the equivalence does not hold, DeepSec also displays the corresponding attack trace.

Note that **DeepSec** can take several files as input. Ex: `deepsec file1 file2 file3`

### Distributed computation

By default, **DeepSec** does not distribute the computation. To activate the distributed computation, `deepsec` should be run with the option `-distributed n` where `n` is the number of available local cores. It is also possible to distribute computation through several computers. To do so, deepsec requires an ssh connexion between the localhost and the distant machine. The computation on distant machine must be configured with the option `-distant_workers <host> <path> <n>`. The parameter `<host>` is the ssh login and address (e.g my_login@my_host). The parameter `<path>` should indicate the path on the distant machine the deepsec directory. Finally the parameter `<n>` represents the number of cores that should be dedicated by this distant machine to the computation of the input file. As connections to distant machines are performed through ssh we recommend to configure a passwordless authentication, e.g., using ssh keys.

Note that that the option `-distant_workers` should be used for each distant machine.

```
deepsec -distributed 20 -distant_workers login1@host1 tools/deepsec 15 -distant_workers login2@host2 deepsec 35 my_file.dps
```

In this command line, the first machine should be accessible with `ssh login1@host1` and the **DeepSec** directory should be located at `~/tools/deepsec` on this machine. Similarly, the second machine should be accessible with `ssh login2@host1` and the **DeepSec** directory should be located at `~/deepsec`. If the connexions to both machines are successful, **DeepSec** will distribute the computation of the file `my_file.dps` between 20 local cores, 15 cores on the first machine and 35 on the second machine.

**_IMPORTANT_**: The localhost and distant machines should have exactly the same version of **DeepSec** (The Git hash is displayed when running `deepsec` without parameters or with the option `-help`) compiled with the same version of **OCaml**.
