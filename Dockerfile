FROM ubuntu:22.04
ARG DEBIAN_FRONTEND=noninteractive

SHELL ["/bin/bash", "-c"]

RUN apt-get update -y -q \
 && apt-get install -y -q --no-install-recommends \
   ca-certificates \
   curl \
   libgmp-dev \
   m4 \
   ocaml \
   opam \
   rsync \
   sudo \
   libgmp-dev python3

# Install OCaml and Coq 
RUN opam init --auto-setup --yes --bare --disable-sandboxing \
   && opam switch create system ocaml-system \
   && eval $(opam env) \ 
   && opam repo add --all-switches --set-default coq-released https://coq.inria.fr/opam/released \
   && opam pin add -y -k version -j "$(nproc)" coq 8.13.2 \
   && opam clean -a -c -s --logs

# Install Rust  
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}" 

# Copy over proofs and compilers directory 
RUN mkdir -p /home/RichWasm
COPY ./compilers  /home/RichWasm/compilers
COPY ./theories   /home/RichWasm/coq-proof

# Install OCaml compilers for ML, L3 to RichWasm
WORKDIR /home/RichWasm/compilers
RUN opam switch create 5.0.0 \ 
   && eval $(opam env --switch=5.0.0) \
   && opam option depext=false \
   && opam install . --yes \ 
   && opam install core_unix --yes \
   && dune build ml l3 rich_wasm 

# Build compilers and run tests for ML, L3 and the RichWasm annotator 
#   && dune build ml l3 rich_wasm \
#   && dune runtest ml l3 rich_wasm 

# Install Coq to compile proofs 
WORKDIR /home/RichWasm/coq-proof
RUN opam switch create 4.08.1 \ 
   && eval $(opam env --switch=4.08.1) \ 
   && opam install coq.8.13.2 --yes \ 
   && opam repo add coq-released https://coq.inria.fr/opam/released \ 
   && opam install coq-ext-lib.0.11.5 --yes 

# To compile the proofs 
# RUN eval $(opam env --switch=4.08.1) && make Coq.Makefile && make

WORKDIR /home/RichWasm/compilers/richwasm 
RUN cargo build 

WORKDIR /
