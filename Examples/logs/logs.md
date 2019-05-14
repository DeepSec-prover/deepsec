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
  - DeepSec session: 2s (1 core), 1s (20 cores)

* *4 sessions*
  + 3 identical passports + 1 fresh passport **[violated]**
    - DeepSec vanilla: >12h (1 core), >12h (20 cores)
    - DeepSec session: 2s (1 core), 1s (20 cores)
  + 2 identical passports + 2 fresh passports **[equivalent]**
    - DeepSec vanilla: >12h (1 core), >12h (20 cores)
    - DeepSec session: 128s (1 core), 14s (20 cores)

* *5 sessions*
  + 4 identical passports + 1 fresh passport **[violated]**
    - DeepSec vanilla: >12h (1 core), >12h (20 cores)
    - DeepSec session: 30s (1 core), 3s (20 cores)
  + 3 identical passports + 2 fresh passports **[violated]**
    - DeepSec vanilla: >12h (1 core), >12h (20 cores)
    - DeepSec session: ??? (1 core), 2h47 (20 cores)
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
    - DeepSec vanilla: ??? (1 core), 2h41 (20 cores)
    - DeepSec session: ??? (1 core), ??? (20 cores)
  + revote (Alice x3, Bob x1) **[equivalence]**
    - DeepSec vanilla: ??? (1 core), ??? (20 cores)
    - DeepSec session: ??? (1 core), ??? (20 cores)
  + revote (Alice x2, Bob x2) **[equivalence]**
    - DeepSec vanilla: ??? (1 core), 2h53 (20 cores)
    - DeepSec session: ??? (1 core), ??? (20 cores)
  + revote (Alice x4, Bob x1) **[equivalence]**
    - DeepSec vanilla: ??? (1 core), ??? (20 cores)
    - DeepSec session: ??? (1 core), ??? (20 cores)
  + revote (Alice x3, Bob x2) **[equivalence]**
    - DeepSec vanilla: ??? (1 core), ??? (20 cores)
    - DeepSec session: ??? (1 core), ??? (20 cores)
  + revote (Alice x5, Bob x1) **[equivalence]**
    - DeepSec vanilla: ??? (1 core), ??? (20 cores)
    - DeepSec session: ??? (1 core), ??? (20 cores)
  + revote (Alice x4, Bob x2) **[equivalence]**
    - DeepSec vanilla: ??? (1 core), ??? (20 cores)
    - DeepSec session: ??? (1 core), ??? (20 cores)
  + revote (Alice x3, Bob x3) **[equivalence]**
    - DeepSec vanilla: ??? (1 core), ??? (20 cores)
    - DeepSec session: ??? (1 core), ??? (20 cores)

-------

Scytl
-------

* 5 roles **[equivalence]**
  - DeepSec Vanilla: 56min (1 core), ??? (20 cores)
  - DeepSec session: 1s (1 core), 1s (20 cores)
