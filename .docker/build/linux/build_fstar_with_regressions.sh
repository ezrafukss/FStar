#!/usr/bin/env bash

target=$1
out_file=$2
threads=$3
result_file=result.txt

if [[ -x /usr/bin/time ]]; then
    gnutime=/usr/bin/time
else
    gnutime=""
fi

function export_home() {
  if command -v cygpath >/dev/null 2>&1; then
    export $1_HOME=$(cygpath -m "$2")
  else
    export $1_HOME="$2"
  fi
}

function fetch_vale() {
    if [ ! -d vale ]; then
        git clone https://github.com/project-everest/vale vale
    fi

    cd vale
    git fetch origin
    echo Switching to vale to fstar_ci
    git clean -fdx .
    git reset --hard origin/fstar_ci
    nuget.exe restore tools/Vale/src/packages.config -PackagesDirectory tools/FsLexYacc
    cd ..
    export_home VALE "$(pwd)/vale"
}

# By default, HACL* master works against F* stable. Can also be overridden.
function fetch_hacl() {
    if [ ! -d hacl-star ]; then
        git clone https://github.com/mitls/hacl-star hacl-star
    fi

    cd hacl-star
    git fetch origin
    local ref=$( if [ -f ../.hacl_version ]; then cat ../.hacl_version | tr -d '\r\n'; else echo origin/master; fi )
    echo Switching to HACL $ref
    git reset --hard $ref
    cd ..
    export_home HACL "$(pwd)/hacl-star"
    export_home EVERCRYPT "$(pwd)/hacl-star/providers"
}

# By default, kremlin master works against F* stable. Can also be overridden.
function fetch_kremlin() {
    if [ ! -d kremlin ]; then
        git clone https://github.com/FStarLang/kremlin kremlin
    fi

    cd kremlin
    git fetch origin
    local ref=$( if [ -f ../.kremlin_version ]; then cat ../.kremlin_version | tr -d '\r\n'; else echo origin/master; fi )
    echo Switching to KreMLin $ref
    git reset --hard $ref
    cd ..
    export_home KREMLIN "$(pwd)/kremlin"
}

function fetch_and_make_kremlin() {
  fetch_kremlin
  
  # Default build target is minimal, unless specified otherwise
  local target
  if [[ $1 == "" ]]; then
    target="minimal"
  else
    target="$1"
  fi

  make -C kremlin $PARALLEL_OPT $target || \
    (cd kremlin && git clean -fdx && make $PARALLEL_OPT $target)
  export PATH="$(pwd)/kremlin:$PATH"
}

# By default, mitls-fstar master works against F* stable. Can also be overridden.
function fetch_mitls() {
    if [ ! -d mitls-fstar ]; then
        git clone https://github.com/mitls/mitls-fstar mitls-fstar
    fi
    cd mitls-fstar
    git fetch origin
    local ref=$( if [ -f ../.mitls_version ]; then cat ../.mitls_version | tr -d '\r\n'; else echo origin/master; fi )
    echo Switching to mitls-fstar $ref
    git reset --hard $ref
    cd ..
    export_home MITLS "$(pwd)/mitls-fstar"
}

function do_tests () {
    if ! make -C src -j $threads utest-prelude
    then
        echo Warm-up failed
        echo Failure > $result_file
    else
        fetch_vale &
        fetch_hacl &
        fetch_and_make_kremlin &
        fetch_mitls &
        { 
            if [ ! -d hacl-star-old ]; then
                git clone https://github.com/mitls/hacl-star hacl-star-old
                cd hacl-star-old && git reset --hard 98755f79579a0c153140e8d9a186145beafacf8f
            fi 
        } &
        wait

        # The commands above were executed in sub-shells and their EXPORTs are not
        # propagated to the current shell. Re-do.
        export_home HACL "$(pwd)/hacl-star"
        export_home KREMLIN "$(pwd)/kremlin"
        export_home FSTAR "$(pwd)"

        # $status_file is the name of a file that contains true if and
        # only if the F* regression suite failed, false otherwise
        # $orange_status_file is the name of a file that contains true
        # if and only if some additional regression suite (HACL*,
        # miTLS) broke, false otherwise
        local status_file="status.txt"
        local orange_status_file="orange_status.txt"
        echo false > $status_file
        echo false > $orange_status_file
        
        # Once F* is built, run its main regression suite, along with more relevant
        # tests.
        { $gnutime make -C src $PARALLEL_OPT -k $target && echo -n true > $status_file; } &

        { cd vale
          if [[ "$OS" == "Windows_NT" ]]; then
              timeout 480 ./scons_cygwin.sh -j 4 --FSTAR-MY-VERSION --MIN_TEST
          else
              timeout 480 scons -j 4 --FSTAR-MY-VERSION --MIN_TEST
          fi || {
              echo "min-test (Vale)" >> $ORANGE_FILE
              echo true > $orange_status_file
          }
          cd ..
        } &

        { OTHERFLAGS='--use_two_phase_tc false --warn_error -276 --use_hint_hashes' timeout 480 make -C hacl-star/code/hash/ -j 4 Hacl.Impl.SHA2_256.fst-verify || {
              echo "Hacl.Hash.SHA2_256.fst-verify (HACL*)" >> $ORANGE_FILE
              echo true > $orange_status_file
          }
        } &

        { OTHERFLAGS='--use_hint_hashes' timeout 480 make -C hacl-star/secure_api -f Makefile.old -j 4 aead/Crypto.AEAD.Encrypt.fst-ver || {
              echo "Crypto.AEAD.Encrypt.fst-ver (HACL*)" >> $ORANGE_FILE
              echo true > $orange_status_file
          }
        } &

        # TODO: remove this hacl-old clone once we manage to get an updated StreamAE
        # on the verify branch of miTLS
        { HACL_HOME=$(pwd)/hacl-star-old OTHERFLAGS='--use_two_phase_tc false --use_hint_hashes' timeout 480 make -C mitls-fstar/src/tls -j 4 StreamAE.fst-ver || {
              echo "StreamAE.fst-ver (mitls)" >> $ORANGE_FILE
              echo true > $orange_status_file
          }
          # NS: removed this until some other suitable targets are restored in miTLS' verify branch
          # #run additional tests on the verify branch, currently hardcoded
          # cd mitls-fstar
          # git reset --hard origin/verify
          # cd ..
          # OTHERFLAGS=--use_hint_hashes timeout 240 make -C mitls-fstar/src/tls $PARALLEL_OPT Mem.fst-ver || \
              # echo "Mem.fst-ver (mitls verify)" >> $ORANGE_FILE;
          # OTHERFLAGS=--use_hint_hashes timeout 240 make -C mitls-fstar/src/tls $PARALLEL_OPT Pkg.fst-ver || \
              # echo "Pkg.fst-ver (mitls verify)" >> $ORANGE_FILE;
        } &

        # JP: doesn't work because it leads to uint128 being verified in the wrong Z3
        # context (?) meaning that some proof obligations fail
        # { cd kremlin/test && timeout 480 ../krml -warn-error @4 -static-header FStar -no-prefix \
            #     Test128 Test128.fst -verify -verbose -fnouint128 -tmpdir .output/Test128.out || \
            #   echo "test/Test128.test (KreMLin)" >> $ORANGE_FILE; } &

        # { cd kremlin/test && timeout 480 ../krml -warn-error @4 -add-include '"kremstr.h"' \
            #     main-Server.c -tmpdir .output/Server.out -no-prefix Server -verify \
            #     Server.fst -verbose || \
            #   echo "test/Server.test (KreMLin)" >> $ORANGE_FILE; } &
        wait

        # Make it an orange if there's a git diff. Note: FStar_Version.ml is in the
        # .gitignore.
        echo "Searching for a diff in src/ocaml-output"
        if ! git diff --exit-code --name-only src/ocaml-output; then
            echo "GIT DIFF: the files in the list above have a git diff"
            echo "snapshot-diff (F*)" >> $ORANGE_FILE
            echo true > $orange_status_file
        fi

        if $(cat $status_file) ; then
            echo "F* regression failed"
            echo Failure > $result_file
        elif $(cat $orange_status_file) ; then
            echo "F* regression had breakages"
            echo Success with breakages > $result_file
        else
            echo "F* regression succeeded"
            echo Success > $result_file
        fi
        rm $status_file $orange_status_file
    fi
}

tail -f $out_file &
tail_pd=$!
{ do_tests 3>&1 1>&2 2>&3 | sed 's!^![STDERR]!' 3>&1 1>&2 2>&3 | sed 's!^![STDOUT] !' 2>&1 ; } >> $out_file
kill $tail_pd