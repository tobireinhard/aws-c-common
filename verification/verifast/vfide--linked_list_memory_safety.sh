cd `dirname $0`
script_dir=`pwd`


# TODO: Set path to VeriFast directory.
vf_dir=""
if [[ "$vf_dir" == "" ]]
then
  echo "TODO: Set path to Veriast directory."
  echo "Aborting."
  exit
fi


# TODO: Set installed VeriFast version.
vf_version=""
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


if [[ $1 == "" || $1 == "ide" ]]
then
  vf_select=$vfide
  codeFontFlag="-codeFont"
  traceFontFlag="-traceFont"
  fontSize="17"
elif [[ $1 == "console" ]]
then
  vf_select=$vf
  verboseFlag="-verbose"
  verbosity_level="1"
fi

if [[ $vf_select == "" ]]
then
  echo "No verifast version selected."
  echo "Aborting."
  exit
fi

echo
$vf_select $codeFontFlag $fontSize $traceFontFlag $fontSize $verboseFlag $verbosity_level \
  -I "$include_dir" \
  -I "$include_cbmc_dir" \
  -D "VERIFAST" \
  "$vf_proof_dir/linked_list_inl--memory_safety.c"
