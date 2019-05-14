---
title: "Experiments DeepSec"
pagetitle: "notes"
author: ""
header-includes:
   - \usepackage[english]{chetor_md}
fontsize: 11pt
---

-------

BAC
-------

* *2 sessions* **[violated]**
  - DeepSec vanilla: <1s (1 core), <1s (20 cores)
  - DeepSec session: <1s (1 core), <1s (20 cores)

* *3 sessions* **[violated]**
  - DeepSec vanilla: >12h (1 core), >12h (20 cores)
  - DeepSec session: ??? (1 core), ??? (20 cores)

* *4 sessions*
  + 3 identical passports + 1 fresh passport **[violated]**
    - DeepSec vanilla: >12h (1 core), >12h (20 cores)
    - DeepSec session: ??? (1 core), ??? (20 cores)
  + 2 identical passports + 2 fresh passports **[equivalent]**
    - DeepSec vanilla: >12h (1 core), >12h (20 cores)
    - DeepSec session: ??? (1 core), ??? (20 cores)

* *5 sessions*
  + 4 identical passports + 1 fresh passport **[violated]**
    - DeepSec vanilla: >12h (1 core), >12h (20 cores)
    - DeepSec session: ??? (1 core), ??? (20 cores)
  + 3 identical passports + 2 fresh passports **[violated]**
    - DeepSec vanilla: >12h (1 core), >12h (20 cores)
    - DeepSec session: ??? (1 core), ??? (20 cores)
  + 2 identical passports + 3 fresh passports **[???]**
    - DeepSec vanilla: >12h (1 core), >12h (20 cores)
    - DeepSec session: ??? (1 core), ??? (20 cores)


-------

Helios
-------

* *Vanilla* **[violated]**
  - DeepSec vanilla: <1s (1 core), <1s (20 cores)
  - DeepSec session: <1s (1 core), <1s (20 cores)

* *Helios Weeding*
  + no revote **[equivalence]**
    - DeepSec vanilla: 3s (1 core), 1s (20 cores)
    - DeepSec session: <1s (1 core), 1s (20 cores)
  + revote (Alice x2, Bob x1) **[violated]**
    - DeepSec vanilla: 1s (1 core), 2s (20 cores)
    - DeepSec session: <1s (1 core), <1s (20 cores)

* *Helios ZKP*
  + no revote **[equivalence]**
    - DeepSec vanilla: 3s (1 core), 2s (20 cores)
    - DeepSec session: <1s (1 core), <1s (20 cores)
  + revote (Alice x2, Bob x1) **[equivalence]**
    - DeepSec vanilla: >12h (1 core), 2h41 [redo?] (20 cores)
    - DeepSec session: 16min (1 core), 1min10 (20 cores)
  + revote (Alice x3, Bob x1) **[equivalence]**
    - DeepSec vanilla: >12h (1 core), >12h (20 cores)
    - DeepSec session: 44min (1 core), 2min41 (20 cores)
  + revote (Alice x2, Bob x2) **[equivalence]**
    - DeepSec vanilla: >12h (1 core), 2h53 (20 cores)
    - DeepSec session: 50min (1 core), 3min27 (20 cores)
  + revote (Alice x4, Bob x1) **[equivalence]**
    - DeepSec vanilla: >12h (1 core), >12h (20 cores)
    - DeepSec session: 2h18 (1 core), 6min34 (20 cores)
  + revote (Alice x3, Bob x2) **[equivalence]**
    - DeepSec vanilla: >12h (1 core), >12h (20 cores)
    - DeepSec session: 3h15 (1 core), 8min28 (20 cores)
  + revote (Alice x5, Bob x1) **[equivalence]**
    - DeepSec vanilla: >12h (1 core), >12h (20 cores)
    - DeepSec session: SINCE 7:49PM (1 core), 13min (20 cores)
  + revote (Alice x4, Bob x2) **[equivalence]**
    - DeepSec vanilla: >12h (1 core), >12h (20 cores)
    - DeepSec session: ??? (1 core), 18min (20 cores)
  + revote (Alice x3, Bob x3) **[equivalence]**
    - DeepSec vanilla: >12h (1 core), >12h (20 cores)
    - DeepSec session: ??? (1 core), 19min (20 cores)
  + revoteMAX (Alice x7, Bob x4) **[equivalence]**
    - DeepSec vanilla: >12h (1 core), >12h (20 cores)
    - DeepSec session: ??? (1 core), ??? (20 cores)

-------

Scytl
-------

* 5 roles **[equivalence]**
  - DeepSec vanilla: 56min (1 core), 3min8 (20 cores)
  - DeepSec session: 1s (1 core), 1s (20 cores)


-------

Running example paper
-------

* 2 honnest voters, 1 dishonnest voter (model parallel mixnet) **[equivalence]**
  - DeepSec vanilla: 1min41 (1 core)
  - DeepSec session: `false attack` (1 core)

* 2 honnest voters, 1 dishonnest voter **[equivalence]**
  - DeepSec vanilla: 15s (1 core)
  - DeepSec session: <1s (1 core)

* 2 honnest voters, 2 dishonnest voters **[equivalence]**
  - DeepSec vanilla: 30min (1 core)
  - DeepSec session: <1s (1 core)

* 2 honnest voters, 3 dishonnest voters **[equivalence]**
  - DeepSec vanilla: >12h (1 core)
  - DeepSec session: 68s (1 core)



-------

AKA
-------

* anonymity
  + 3 sessions **[equivalence]**
    - DeepSec vanilla: 30s (20 cores)
    - Deepsec session: ??? (20 cores)
