permit(
  principal is a in a::"\0",
  action == Action::"action",
  resource == a::"\0"
) when {
  ((true && (((true == false) == (false == true)) == (false == (true == false)))) && (false == principal)) && principal
};
