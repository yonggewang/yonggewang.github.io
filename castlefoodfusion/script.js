const tabs=[...document.querySelectorAll('.tab')];
const cards=[...document.querySelectorAll('.dish-card')];
const search=document.getElementById('search');
const empty=document.getElementById('no-results');
let activeCategory='all';
function updateMenu(){
  const term=search.value.trim().toLowerCase(); let count=0;
  cards.forEach(card=>{
    const categoryOk=activeCategory==='all'||card.dataset.category===activeCategory||(activeCategory==='vegetarian'&&card.dataset.category==='vegetarian');
    const searchOk=!term||(card.dataset.search+' '+card.textContent).toLowerCase().includes(term);
    const show=categoryOk&&searchOk;card.hidden=!show;if(show)count++;
  });
  empty.hidden=count>0;
}
tabs.forEach(tab=>tab.addEventListener('click',()=>{
  activeCategory=tab.dataset.category;
  tabs.forEach(t=>{const selected=t===tab;t.classList.toggle('active',selected);t.setAttribute('aria-selected',String(selected));});
  updateMenu();
}));
search.addEventListener('input',updateMenu);
const toggle=document.querySelector('.menu-toggle'),nav=document.querySelector('.nav');
toggle.addEventListener('click',()=>{const open=nav.classList.toggle('open');toggle.setAttribute('aria-expanded',String(open));});
nav.querySelectorAll('a').forEach(a=>a.addEventListener('click',()=>{nav.classList.remove('open');toggle.setAttribute('aria-expanded','false');}));
document.getElementById('year').textContent=new Date().getFullYear();
