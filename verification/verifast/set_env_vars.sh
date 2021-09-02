echo
echo "======================================"
echo
echo "Setting environment varables"
echo

vf_dir_abs=$1
if [[ "$vf_dir_abs" == "" ]]
then
  echo "Did not receive absolute path to VeriFast directory as argument."
  echo "Aborting."
  exit
fi


vf_version=$2    # e.g. "509f16f"
if [[ "$vf_version" == "" ]]
then
  echo "Did not receive VeriFast version as argument."
  echo "Aborting."
  exit
fi


echo VeriFast verion : $vf_version
echo

export PATH="/usr/local/vfdeps-$vf_version/bin:$PATH"
echo '$PATH' :
echo "'$PATH'"
echo

export DYLD_LIBRARY_PATH="/usr/local/vfdeps-$vf_version/lib:$DYLD_LIBRARY_PATH"
echo '$DYLD_LIBRARY_PATH' :
echo "'$DYLD_LIBRARY_PATH'"
echo


export vf="$vf_dir/bin/verifast"
export vfide="$vf_dir/bin/vfide"
echo '$vf' :
echo $vf
echo '$vfide' :
echo $vfide
echo
