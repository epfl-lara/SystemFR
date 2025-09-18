FROM rocq/rocq-prover:9.0
RUN opam update && opam install -y rocq-equations.1.3.1+9.0
WORKDIR /theories-local
VOLUME /theories-local
CMD ["bash", "-l", "-c", "cp -r /theories/*.v /theories/configure /theories-local && ./configure && TIMED= TIMECMD= make -j8"]
