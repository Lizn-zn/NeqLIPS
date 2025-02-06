#!/bin/bash

# Save the current directory
WORKDIR=$(pwd)

# Update apt-get and install dependencies
sudo apt-get update
sudo apt-get install -y \
    wget \
    sudo \
    expect \
    cargo \
    unzip \
    g++ \
    && sudo apt-get clean

# Go to /NeqLIPS directory and update git submodules
cd $WORKDIR
git submodule init && git submodule update

cd $WORKDIR/Installation
# Check if conda is installed
if ! command -v conda &> /dev/null; then
    echo "Conda not found, installing Anaconda..."
    # Download and install Anaconda if conda is not found
    wget https://repo.anaconda.com/archive/Anaconda3-2024.06-1-Linux-x86_64.sh
    sh Anaconda3-2024.06-1-Linux-x86_64.sh -b -f
    # Add Anaconda to PATH by modifying .bashrc
    echo "export PATH=~/anaconda3/bin:\$PATH" >> ~/.bashrc
    # Reload .bashrc to update the PATH
    source ~/.bashrc
    conda init
    echo "Anaconda installed successfully."
else
    echo "Conda is already installed."
fi
conda env create -f env.yml

# Install mtsolve package via pip
conda activate NeqLIPS && pip install git+https://github.com/Lizn-zn/pysmt.git@Bottema \
    && pip install --force-reinstall git+https://github.com/Lizn-zn/MT-Solver.git

# Maple installation check
if ! command -v maple &> /dev/null; then
    echo "Maple does not exist, try install Maple..."
    # Check if the Maple installer exists before running it
    if [ -f "$WORKDIR/Installation/Maple2024.0LinuxX64Installer.run" ]; then
        ./Maple2024.0LinuxX64Installer.run --mode unattended --desktopshortcut 0 --installdir $WORKDIR/Installation/Maple2024
        # Copy necessary files to installation directory
        cp ./medicine/libmaple.so $WORKDIR/Installation/Maple2024/bin.X86_64_LINUX
        cp ./medicine/license.dat $WORKDIR/Installation/Maple2024/license
        # Add Maple to PATH in .bashrc
        echo "export PATH=\$PATH:$WORKDIR/Installation/Maple2024/bin" >> ~/.bashrc
        echo "Maple installed successfully."
    else
        echo "Maple installer not found. Please make sure the installer is located at $WORKDIR/Installation/Maple2024.0LinuxX64Installer.run"
    fi
else
    echo "Maple already exists."
fi

# Mathematica installation check
if ! command -v wolfram &> /dev/null; then
    echo "Mathematica does not exist, try install Mathematica..."
    if [ -f "$WORKDIR/Installation/Wolfram_14.1.0_LIN.sh" ]; then
        echo "Mathematica Installation exists"
        cd $WORKDIR/Installation/Wolfram2024
        sh Wolfram_14.1.0_LIN.sh -- -auto -targetdir=$WORKDIR/Installation/MMA2024
        ./activate_wolfram.expect
    else
        echo "Mathematica installer not found. Please make sure the installer is located at $WORKDIR/Installation/Wolfram_14.1.0_LIN.sh"
    fi
else
    echo "Mathematica already exists."
fi

# Egg Matching installation
cd $WORKDIR/LIPS/egg_matching
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
. "$HOME/.cargo/env"
cargo install maturin
conda activate NeqLIPS && maturin develop --release

# Lean installation
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
echo "source \$HOME/.elan/env" >> ~/.bashrc
source ~/.bashrc
cd $WORKDIR/Neq/math
elan default leanprover/lean4:v4.11.0
lake exe cache get
lake build

# Return to the original directory
cd $WORKDIR

# Completion message
echo "Setup complete!"
