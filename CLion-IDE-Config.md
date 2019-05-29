## WSL guide

#### Setup:
 - [install WSL](https://docs.microsoft.com/en-us/windows/wsl/install-win10) (Ubuntu)
 - open the Ubuntu terminal
 - clone SeaHorn somewhere, eg. `git clone https://github.com/seahorn/seahorn.git /home/user/path/to/seahorn`
 - install basic packages: see [https://github.com/seahorn/seahorn/blob/master/docker/seahorn-build.Dockerfile#L16] for a full list of dependencies (switch to the branch you're working on if necessary)
 - install CLion on Ubuntu:
   - `wget https://download.jetbrains.com/cpp/CLion-2019.1.3.tar.gz`
   - unpack into a folder (should be named `/path/to/apps/folder/clion-year.version`)
   - run `/path/to/apps/folder/clion-year.version/bin/clion.sh`
   - if it fails due to no display:
     - install [XLaunch](https://sourceforge.net/projects/xming) on Windows and run
     - on Ubuntu, `export DISPLAY=:0` (`:0` is the default value for XLaunch - you may have a different value)
   - select the default settings for CLion

#### Initial Build:
 - build the project once by following the steps [here](https://github.com/seahorn/seahorn/tree/master) (switch to the branch you're working on if necessary)
 eg.
```
cmake -DCMAKE_INSTALL_PREFIX=run -DCMAKE_BUILD_TYPE="Release" -DCMAKE_CXX_COMPILER="clang++-6.0" -DCMAKE_C_COMPILER="clang-6.0" -DSEA_ENABLE_LLD="ON" -GNinja -DCMAKE_EXPORT_COMPILE_COMMANDS=1 /path/to/seahorn
ninja extra
ninja crab
ninja install
```
 - you may try using the [prebuilt dependencies](https://github.com/seahorn/seahorn-ext-deps/releases) for a faster initial build, in which case add the flags `-DBOOST_ROOT=/path/to/boost -DLLVM_DIR=/path/to/llvm -DZ3_ROOT=/path/to/z3`
 - once built, there should be a `compile_commands.json` file in your build directory - copy this into the directory where SeaHorn was cloned
 - open CLion if you haven't already and open a project (File -> Open or simply Open from the start window)
 - navigate to the `compile_commands.json` file inside the **SeaHorn** folder and select it

At this point, you should be able to use CLion's code indexing features on source files of the project.

#### Remote Execution and Debugging
 - follow the guide [here](https://www.jetbrains.com/help/clion/remote-projects-support.html) to setup remote deployment, but do not change the default compiler toolchain as this will break code indexing
