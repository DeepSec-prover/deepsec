# FILES
DISTRIBUTED: 10 cores
NON-DISTRIBUTED: 1 core
TIME: total computation time
TIME-withoutPorridge.txt: total time - runtime(Porridge)
EXPLO: number of DeepSec explorations (symbolic states explored)

TimeOut: 2 hours real-time
MemOut: >= 10 GO of RAM or Stack overflow (Porridge)

# COMMANDS
usage: extract_res.py [-h] [--latex LATEX] [--explo EXPLO]
                      [--logs [LOGS [LOGS ...]]]
		                            [--distributed [DISTRIBUTED [DISTRIBUTED ...]]]
					                          [--explos EXPLOS] [--noPorridge NOPORRIDGE]

Extract results of benchmarks from log files.

optional arguments:
  -h, --help            show this help message and exit
    --latex LATEX         you can choose to write all extracted results in a
                            Latex file
			      --explo EXPLO         to display number of explorations instead of time
			        --logs [LOGS [LOGS ...]]
				                        location of log files. Default=.
							  --distributed [DISTRIBUTED [DISTRIBUTED ...]]
							                          only focus on benchmarks carried out with a certain
										                          number of cores (0=not distrivuted).
													    --explos EXPLOS       only show numebr of explorations
													      --noPorridge NOPORRIDGE
													                              time without porridge



./extract_res.py --noPorridge 0 --logs PD/ > RESULTS_NOT-DISTRIBUTED_TIME-withoutPorridge.txt; ./extract_res.py --explos 0 --logs PD/ > RESULTS_NOT-DISTRIBUTED_EXPLOS.txt; ./extract_res.py --logs PD/ > RESULTS_NOT_DISTRIBUTED_TIME.txt
./extract_res.py --noPorridge 0 > RESULTS_DISTRIBUTED_TIME-withoutPorridge.txt; ./extract_res.py --explos 0 > RESULTS_DISTRIBUTED_EXPLOS.txt; ./extract_res.py > RESULTS_DISTRIBUTED_TIME.txt
