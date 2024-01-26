@r("")
forbid(
  principal in a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  (true && (if action then ((!action) || (action || action)) else ((action || action) || (action || action)))) && (((principal || principal) || principal) || principal)
};
