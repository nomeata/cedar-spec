permit(
  principal == a::"",
  action,
  resource == a::""
) when {
  true && (!([false, principal] has ".wlj"))
};
