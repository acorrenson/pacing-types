FROM rocq/rocq-prover:latest
COPY --chown=rocq ./theories/*.v /home/rocq/theories/
COPY --chown=rocq _CoqProject /home/rocq/
COPY --chown=rocq Makefile /home/rocq/
WORKDIR /home/rocq