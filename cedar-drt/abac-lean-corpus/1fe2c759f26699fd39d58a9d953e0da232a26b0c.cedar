permit(
  principal,
  action,
  resource is a in a::""
) when {
  (true && (((a::"" in a::"") in (action in "")) in action)) && action
};
