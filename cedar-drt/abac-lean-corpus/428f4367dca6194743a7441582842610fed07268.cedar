permit(
  principal == a::"",
  action,
  resource in a::""
) when {
  true && [false, context, a::"", action]
};
