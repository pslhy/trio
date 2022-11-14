
## setting & make
```
. setenv
make
```


## run example
option -print-data prints Solution Size and CEGIS Iter times.
```
burst/BurstCmdLine.exe -use-trio burst/benchmarks/io/list_append.mls

burst/BurstCmdLine.exe -print-data -use-trio burst/benchmarks/ref/list_fold.mls
```
