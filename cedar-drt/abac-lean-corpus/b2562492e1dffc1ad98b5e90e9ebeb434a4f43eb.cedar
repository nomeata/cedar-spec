permit(
  principal == a::"",
  action,
  resource in a::"\0"
) when {
  true && [true, principal, context, false]
};
