FROM continuumio/anaconda3:main

USER root
SHELL ["/bin/bash", "-c"]

RUN apt-get update && \
    apt-get install -y \
    wget \
    sudo \
    expect \
    cargo \
    unzip \
    g++ \
    && apt-get clean

COPY . /NeqLIPS

# REPL
WORKDIR /NeqLIPS
RUN git submodule update

# conda environment
WORKDIR /NeqLIPS/Installation
RUN conda env create -f env.yml
SHELL ["conda", "run", "-n", "NeqLIPS", "/bin/bash", "-c"]
RUN echo "conda activate NeqLIPS" >> ~/.bashrc

# mtsolve installation
RUN pip install git+https://github.com/Lizn-zn/pysmt.git@Bottema \
    && pip install --force-reinstall git+https://github.com/Lizn-zn/MT-Solver.git

# Maple Installation
RUN if [ -d "/NeqLIPS/Installation/Maple2024.0LinuxX64" ]; then \
        echo "Maple Installation exists" && \
        cd /NeqLIPS/Installation/Maple2024.0LinuxX64 && \
        ./Maple2024.0LinuxX64Installer.run --mode unattended --desktopshortcut 0 --installdir /NeqProver/Maple2024 && \
        cp ./medicine/libmaple.so /NeqProver/Maple2024/bin.X86_64_LINUX && \
        cp ./medicine/license.dat /NeqProver/Maple2024/license && \
        echo "export PATH=\$PATH:/NeqProver/Maple2024/bin" >> /root/.bashrc; \
    else \
        echo "Maple Installation does not exist"; \
    fi

# Mathematica Installation
RUN if [ -d "/NeqLIPS/Installation/MMA2024" ]; then \
        echo "Mathematica Installation exists" && \
        cd /NeqLIPS/Installation/MMA2024 && \
        sh Wolfram_14.1.0_LIN.sh -- -auto && \
        ./activate_wolfram.expect \
    else \
        echo "Mathematica Installation does not exist"; \
    fi

# Egg Installation
RUN cd /NeqLIPS/LIPS/egg_matching && \
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh  -s -- -y && \
    . "$HOME/.cargo/env" && \
    cargo install maturin && maturin develop --release

# Lean Installation
WORKDIR /NeqLIPS/Lean4
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
RUN echo "source $HOME/.elan/env" >> ~/.bashrc
RUN cd /NeqLIPS/Neq/math && lake exe cache get && lake build

WORKDIR /NeqLIPS/

# CMD ["/bin/bash", "-c", "sh test.sh"]