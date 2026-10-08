FROM rocq/rocq-prover:9.1

ARG STDPP_VERSION=1.13.0

RUN opam update -y \
    && opam install -y "rocq-stdpp.${STDPP_VERSION}" \
    && opam clean -a -c -s --logs

USER root

RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
        python3 \
        python3-pip \
        python3-venv \
        ripgrep \
        tree \
        vim \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

USER rocq

RUN mkdir -p /home/rocq/project

WORKDIR /home/rocq/project

COPY --chown=rocq:rocq . .

# Building the image also checks every Rocq source file.
RUN make build

# Recheck the development when the container is run without another command.
CMD ["make", "build"]
