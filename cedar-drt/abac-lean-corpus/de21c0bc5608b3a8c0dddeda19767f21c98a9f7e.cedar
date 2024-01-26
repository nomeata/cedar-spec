permit(
  principal is a in a::"\0\0\0\0\0\0\0",
  action in [Action::"action"],
  resource
) when {
  ((true && (((!(action <= action)) == (!(a::"\0\0\0\0\0\0\0" <= a::"\0\0\0\0\0\0\0"))) == ((Action::"action" == action) <= false))) && (!(true <= true))) && (((true == action) == (!false)) == principal)
};
