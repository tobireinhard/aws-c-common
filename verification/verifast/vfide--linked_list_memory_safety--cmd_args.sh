cd `dirname $0`
script_dir=`pwd`


# TODO: Set path to VeriFast directory.
vf_dir="$1"
if [[ "$vf_dir" == "" ]]
then
  echo "TODO: Set path to Veriast directory."
  echo "Aborting."
  exit
fi


# TODO: Set installed VeriFast version.
full_vfdeps_name=`ls /usr/local/ | grep vfdeps`
vf_version=${full_vfdeps_name#"vfdeps-"}
if [[ "$vf_version" == "" ]]
then
  echo "TODO: Set installed VeriFast version, e.g., '509f16f'."
  echo "Aborting."
  exit
fi

source ./set_env_vars.sh "$vf_dir" "$vf_version"

aws_c_common_dir=`cd $script_dir/../..; pwd`
vf_proof_dir="$script_dir"
source_dir="$aws_c_common_dir/source"
include_dir="$aws_c_common_dir/include"
include_cbmc_dir="$aws_c_common_dir/verification/cbmc/include"



codeFontFlag=""
traceFontFlag=""
fontSize=""
verboseFlag=""
verbosity_level=""


echo
$vfide -codeFont $fontSize -traceFont $fontSize \
  -I "$include_dir" \
  -I "$include_cbmc_dir" \
  -D "VERIFAST" \
  "$vf_proof_dir/linked_list_inl--memory_safety.c"
