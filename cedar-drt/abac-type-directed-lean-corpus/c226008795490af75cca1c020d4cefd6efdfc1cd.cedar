permit(
  principal,
  action,
  resource in a::""
) when {
  ((true && (!([principal].containsAny([principal])))) && (resource in resource)) && (a::"" in Action::"action")
};
