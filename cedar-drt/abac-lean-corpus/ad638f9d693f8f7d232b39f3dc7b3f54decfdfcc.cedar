permit(
  principal,
  action,
  resource in a::""
) when {
  ((true && (((a::"" == action) == principal) <= action)) && true) && action
};
