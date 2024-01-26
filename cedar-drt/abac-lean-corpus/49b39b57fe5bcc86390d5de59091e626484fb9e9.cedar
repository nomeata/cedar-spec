permit(
  principal == a::"j",
  action,
  resource
) when {
  (true && ((a::"j" in (-(""))) in context)) && a::""
};
